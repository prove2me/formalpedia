-- Prove2me | Theorems.Thm_RSSubspaceDesign_theorem_7_2
-- name    : RSSubspaceDesign.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:27.267352+00:00
-- url     : https://prove2.me/theorems/14f9332d-fd82-43fe-b806-6034f314f766
-- title:
--   Theorem 7.2 — explicit effective points over $K$ with $|K|>nr$, of degree $(d+g)^{O(g)}$, found in $|K|^{O_{d,g}(1)}$ time
-- statement:
--   For any fixed integers $r\ge2$, $g\ge2^r$, $d\ge1$, any integer $n\ge g$ and any finite field $K$ with $|K|>nr$, there is an explicit extension field $F/K$ with $[F:K]\le(d+g)^{O(g)}$ and points $\alpha_1,\dots,\alpha_n\in F$ with automorphisms $\sigma_1,\dots,\sigma_g$ such that
--
--   1. $d\le[K(\alpha_i):K]\le2[K(\alpha_j):K]$ for all $i\ne j$;
--   2. $\alpha_i$ and $\alpha_j$ are non-conjugate for $i\ne j$;
--   3. $\sigma_1,\dots,\sigma_g$ generate $\mathrm{Gal}(F/K)$, and $|\{i\in[n]:\sigma_j(\alpha_i)\ne\alpha_i\}|\le\lceil n/g\rceil$ for all $j\in[g]$;
--   4. for every nonzero $K$-subspace $\mathcal Q\subseteq K[X]_{<nr}$ of dimension at most $2^r$,
--   $$\sum_{i=1}^n\max_{0\ne q\in\mathcal Q}\operatorname{mult}_{\alpha_i}q\;\le\;\max_{0\ne q\in\mathcal Q}\deg q.$$
--
--   Moreover, such evaluation points can be found in time $|K|^{O_{d,g}(1)}$.
--
--   Items 3 and 4 say that the points are $(n,g,\lceil n/g\rceil,r)_{F,K}$-effective, the hypothesis of Theorem 4.2.
--
--   **Formalization Note** The construction is one Turing machine per $(r,g,d)$; on input $(p,f,n)$ it outputs $F=K[X]/(h)$ (monic irreducible $h$, $\deg h\le(d+g)^{cg}$ with one absolute $c$) and the points in the power basis of $F/K$ within $|K|^{C}$ steps, $C$ depending on $(r,g,d)$. The automorphisms are asserted to exist.
--
--   Differences from the source:
--   - encoding: every finite field K → K = 𝔽_p[Y]/(f) for a prime p and a monic irreducible f ∈ 𝔽_p[Y], input as (p, f); reason: every finite field is isomorphic to one of these and the statement is invariant under isomorphism
--   - encoding: there exists an explicit extension field F/K and points α₁, …, αₙ; such evaluation points can be found in time |K|^{O_{d,g}(1)} → one multi-stack Turing machine and an exponent C per (r, g, d) that, on input (p, f, n), halts within |K|^C steps with F = K[X]/(h) (coefficient lists of a monic irreducible h) and the points in the power basis of F/K; reason: the paper fixes no machine model; Turing machines simulate any reasonable deterministic model with polynomial overhead, absorbed by |K|^{O(1)}, and every reasonable representation of F and its elements converts to this one in poly(|F|) time
--   - reading: [F : K] ≤ (d + g)^{O(g)} → deg h ≤ (d + g)^{c·g} with one absolute c chosen before r, g, d; reason: O(g) without subscript is an absolute constant times g
--   - reading: Moreover, such evaluation points can be found in time → the machine outputs F and the points; the automorphisms σ₁, …, σ_g are asserted to exist; reason: the sentence names the evaluation points (and the field they live in)
--   - encoding: [K(αᵢ) : K]; non-conjugate → natDegree of the minimal polynomial of αᵢ over K; no K-automorphism of F maps αᵢ to αⱼ; reason: F/K is a finite Galois extension, so the conjugates of αᵢ in F are its images under Gal(F/K)
--   - encoding: the max-form of (4.1); ⌈n/g⌉; nr → MultBound (choice-function form); ⌈(n : ℝ)/g⌉₊; n * r; reason: maxima over the finite set Q ∖ {0} are attained; Lean conventions; same values
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 7.2, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField
import Definitions.Def_RSSubspaceDesign_MultBound

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

open Classical in
/-- **Theorem 7.2 (Explicit effective points).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Theorem 7.2, p.40.

For any fixed integers `r ≥ 2`, `g ≥ 2^r`, `d ≥ 1`, and integer `n ≥ g`, for any finite field `K`
with `|K| > nr`, there exists an explicit extension field `F/K` with `[F : K] ≤ (d + g)^{O(g)}` and
points `α₁, …, αₙ` with automorphisms `σ₁, …, σ_g` such that
* `d ≤ [K(αᵢ) : K] ≤ 2[K(αⱼ) : K]` for all `i ≠ j`;
* `αᵢ` and `αⱼ` are non-conjugate;
* `σ₁, …, σ_g` generate `Gal(F/K)` and `|{i ∈ [n] : σⱼ(αᵢ) ≠ αᵢ}| ≤ ⌈n/g⌉` for all `j ∈ [g]`;
* for every nonzero `K`-subspace `Q ⊆ K[X]_{<nr}` of dimension at most `2^r`, (4.1) holds.
Moreover, such evaluation points can be found in time `|K|^{O_{d,g}(1)}`.

**Formalization Note.** Existence and computation are stated together. `K` is input as a prime `p`
and a monic irreducible `f ∈ 𝔽_p[Y]` (`K = AdjoinRoot f`, `|K| = p^{deg f}`), followed by `n`; every
finite field is isomorphic to one of these. The machine outputs `F = K[X]/(h)` as the coefficient
lists of a monic irreducible `h` and the points in the power basis of `F/K` (`decPoly`,
`IsCoeffList`; decoding by `AdjoinRoot.mk`). The constant `c` of `(d + g)^{O(g)}` is absolute; the
machine and the time exponent `C` depend on the fixed `r, g, d`. `[K(x) : K]` is the degree of the
minimal polynomial of `x` over `K`. Non-conjugate: no `K`-automorphism of `F` maps `αᵢ` to `αⱼ`.
`Gal(F/K)` is `F ≃ₐ[K] F`; the `σⱼ` are only asserted to exist. The last bullet is `MultBound`
(display (4.1) in choice-function form). `⌈n/g⌉` is `⌈(n : ℝ) / g⌉₊`; `nr` is the product `n·r`. -/
theorem theorem_7_2 :
    ∃ c : ℕ, ∀ r g d : ℕ, 2 ≤ r → 2 ^ r ≤ g → 1 ≤ d →
      ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
        ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
        ∀ n : ℕ, g ≤ n → n * r < p ^ f.natDegree →
          ∃ (hc : List (List ℕ)) (ac : List (List (List ℕ))),
            IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc ∧
            ac.length = n ∧ (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
            HMBinPacking.OutputsWithin M (encField p f ++ encNat n)
              (encList (encList encNat) hc ++ encList (encList (encList encNat)) ac)
              ((p ^ f.natDegree) ^ C) ∧
            (decPoly p f hc).Monic ∧ Irreducible (decPoly p f hc) ∧
            (decPoly p f hc).natDegree ≤ (d + g) ^ (c * g) ∧
            (let α : Fin n → AdjoinRoot (decPoly p f hc) :=
                fun i => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i []));
              (∀ i j, i ≠ j → d ≤ (minpoly (AdjoinRoot f) (α i)).natDegree ∧
                  (minpoly (AdjoinRoot f) (α i)).natDegree ≤
                    2 * (minpoly (AdjoinRoot f) (α j)).natDegree) ∧
              (∀ i j, i ≠ j → ∀ τ : AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f]
                  AdjoinRoot (decPoly p f hc), τ (α i) ≠ α j) ∧
              (∃ σ : Fin g → (AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f]
                  AdjoinRoot (decPoly p f hc)),
                Subgroup.closure (Set.range σ) = ⊤ ∧
                ∀ j, (Finset.univ.filter fun i => σ j (α i) ≠ α i).card ≤ ⌈(n : ℝ) / g⌉₊) ∧
              MultBound (AdjoinRoot f) n r α) := by sorry

end RSSubspaceDesign
