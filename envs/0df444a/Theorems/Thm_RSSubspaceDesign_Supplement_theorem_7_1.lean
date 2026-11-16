-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_7_1
-- name    : RSSubspaceDesign.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:43:54.862491+00:00
-- url     : https://prove2.me/theorems/c3a63065-67f8-4249-aeaf-85044f12b85a
-- title:
--   Theorem 7.1 — strongly explicit evaluation points: irreducible $P_1,\dots,P_g$ of distinct prime degrees in $\mathrm{poly}(g,d,\log|K|)$ time, and points in $\beta_j + K$
-- statement:
--   For all integers $g, d \ge 1$ and every finite field $K$, a deterministic algorithm on input $K, g, d$ runs in time $\mathrm{poly}(g, d, \log|K|)$ and outputs irreducible polynomials $P_1, \dots, P_g \in K[X]$ such that
--
--   1. $d \le \deg P_i \le 2\deg P_j \le \mathrm{poly}(d, g)$ for all $i, j$;
--   2. $\{\deg P_i\}_{i \in [g]} \cup \{\mathrm{char}\,K\}$ is a set of $g+1$ distinct primes.
--
--   Moreover, let $n$ be an integer with $\lceil n/g\rceil \le |K|$, let $\beta_1, \dots, \beta_g$ be roots of $P_1, \dots, P_g$, and let $F = K(\beta_1, \dots, \beta_g)$. Let $S_1, \dots, S_g$ be arbitrary subsets of size $\lceil n/g \rceil$ of $\beta_1 + K, \dots, \beta_g + K$, let $\{\alpha_1, \dots, \alpha_n\}$ be an arbitrary subset of $S_1 \cup \dots \cup S_g$, and let
--   $$
--   \sigma_i : x \mapsto x^{|K|^{\prod_{j} \deg P_j / \deg P_i}} .
--   $$
--   Then:
--
--   - $[F : K] \le (d+g)^{O(g)}$;
--   - $d \le [K(\alpha_i):K] \le 2[K(\alpha_j):K]$ for all $i \neq j$;
--   - $\alpha_i$ and $\alpha_j$ are non-conjugate for $i \ne j$;
--   - $\sigma_1, \dots, \sigma_g$ generate $\mathrm{Gal}(F/K)$, and $|\{i \in [n] : \sigma_j(\alpha_i) \neq \alpha_i\}| \le \lceil n/g\rceil$ for every $j$.
--
--   In particular, given an index $i \in [n]$, $\alpha_i$ can be output in time $\mathrm{poly}(\log|F|)$.
--
--   These points satisfy the hypotheses of Theorem 5.1 (with $d = \lceil C(\varepsilon)\rceil$), which gives the strongly explicit codes of Theorem 1.3.
--
--   **Formalization Note** One machine $M$ serves all $g, d, K$, and one absolute $c$ serves every $\mathrm{poly}$ and $O$. Read literally, "for fixed $g, d$ and any $K$ there exists an algorithm" would allow one machine per field, which empties the time bound. $K = \mathbb F_p[Y]/(f)$ is input as $p, f$, then $g, d$, and each $P_i$ is output by its coefficients; $\mathrm{char}\,K = p$. "The roots" are roots in any field $L \supseteq K$, and $F$ is the subfield of $L$ they generate over $K$. The "Moreover" claims are stated for every admissible choice of the $S_j$ and the points. Each $\sigma_i$ is asserted to be a $K$-automorphism of $F$ acting by the displayed power. "In particular" is a second machine $M_2$: on input $(K, g, d, n, i)$ it writes $\alpha_i$ in the monomial basis $\prod_j \beta_j^{e_j}$, $0 \le e_j < \deg P_j$, within $c(\lfloor\log_2|F|\rfloor + 2)^c$ steps, for one admissible choice of sets and points valid for every choice of roots. $\log_2|F|$ is written $\log_2 |K|^{\prod_j \deg P_j}$. Indices are 0-based.
--
--   Differences from the source:
--   - reading: "for any fixed integers g, d ∈ ℕ, for any finite field K, there exists a deterministic algorithm … on input K, g, d" → one machine M for all g, d and K; reason: an algorithm chosen after K makes the time clause empty; the input list (K, g, d) shows the algorithm is uniform
--   - encoding: K a finite field; the output polynomials P_i → K = 𝔽_p[Y]/(f) input as p, f; each P_i by its deg P_i + 1 coefficients; char K = p; reason: every finite field is isomorphic to such an 𝔽_p[Y]/(f); the base mission's machine model
--   - reading: "β₁, …, β_g are the roots of P₁, …, P_g", F = K(β₁, …, β_g) → any roots β_j of P_j in any field L ⊇ K, and F the intermediate field K(β₁, …, β_g) of L; reason: the field generated does not depend on the choice up to K-isomorphism; quantifying over all choices covers the paper's
--   - reading: "In particular, given an index i ∈ [n], α_i can be outputted in time poly(log|F|)" → a second machine M₂ that on input (K, g, d, n, i) outputs α_i in the monomial basis ∏_j β_j^{e_j} (0 ≤ e_j < deg P_j) within c(⌊log₂|F|⌋ + 2)^c steps, for one admissible choice of S_j and points valid for every choice of roots; reason: the clause concerns a computable choice of the arbitrary points; the monomial basis is the natural basis of K(β₁, …, β_g)
--   - encoding: poly(g, d, log|K|); poly(d, g); (d + g)^{O(g)}; poly(log|F|) with log|F| = [F : K] log|K| → c(g + d + ⌊log₂|K|⌋ + 2)^c; c(d + g)^c; (d + g)^{cg}; c(⌊log₂ |K|^{∏_j deg P_j}⌋ + 2)^c, one absolute c; reason: the O-conventions written out; [F : K] = ∏_j deg P_j because the degrees are distinct primes
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 7.1, p.39 (PDF 41)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decK
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

open Classical in
/-- **Theorem 7.1 (Strongly explicit evaluation points).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 7.1, p.39.

For any fixed integers `g, d ∈ ℕ`, for any finite field `K`, there exists a deterministic algorithm
such that on input `K, g, d`, it runs in time `poly(g, d, log |K|)` and outputs irreducible
polynomials `P₁, …, P_g ∈ K[X]` such that:
* `d ≤ deg Pᵢ ≤ 2 deg Pⱼ ≤ poly(d, g)`;
* `{deg Pᵢ}_{i ∈ [g]} ∪ {char K}` is a set of `g + 1` distinct primes.
Moreover, if `n` is an integer with `⌈n/g⌉ ≤ |K|`, `β₁, …, β_g` are the roots of `P₁, …, P_g`,
`F = K(β₁, …, β_g)`, `S₁, …, S_g` are arbitrary sets of size `⌈n/g⌉` of `β₁ + K, …, β_g + K`
respectively, `{α₁, …, αₙ}` is an arbitrary subset of `S₁ ∪ ⋯ ∪ S_g`, and
`σᵢ : x ↦ x^{|K|^{(∏ⱼ deg Pⱼ)/deg Pᵢ}}`, then
* `[F : K] ≤ (d + g)^{O(g)}`;
* `d ≤ [K(αᵢ) : K] ≤ 2[K(αⱼ) : K]` for all `i ≠ j`;
* `αᵢ` and `αⱼ` are non-conjugate;
* `σ₁, …, σ_g` generate `Gal(F/K)`, and `|{i ∈ [n] : σⱼ(αᵢ) ≠ αᵢ}| ≤ ⌈n/g⌉` for all `j ∈ [g]`.
In particular, given an index `i ∈ [n]`, `αᵢ` can be outputted in time `poly(log |F|)`.

**Formalization Note.** `ℕ = {1, 2, …}` (p.10), so `g, d ≥ 1`. One machine `M` for all `g, d, K`
(the literal "for fixed `g, d`, for any `K`, there exists an algorithm" would allow a machine per
`K`, which makes the time clause empty); one absolute `c` serves every `poly` and `O`:
`poly(g, d, log|K|) = c(g + d + ⌊log₂|K|⌋ + 2)^c`, `poly(d, g) = c(d + g)^c`, `(d + g)^{O(g)} =
(d + g)^{cg}`, `poly(log|F|) = c(⌊log₂|F|⌋ + 2)^c`. `K = AdjoinRoot f` is input as `p, f`, then `g, d`;
each `Pᵢ` is output by its `deg Pᵢ + 1` coefficients (`decPoly`). `char K = p`. "The roots" are
roots `βⱼ` of `Pⱼ` in any field `L ⊇ K`; `F` is `K(β₁, …, β_g)` inside `L`, the points are distinct
elements of `F` lying in `⋃ Sⱼ` with `Sⱼ ⊆ βⱼ + K` of size `⌈n/g⌉`; the "Moreover" claims hold for
every such choice. `σᵢ` is asserted to be a `K`-automorphism of `F` given by the displayed power.
`[K(x) : K]` is the degree of the minimal polynomial; non-conjugate: no `K`-automorphism of `F`
maps `αᵢ` to `αⱼ`. "In particular": a second machine `M₂` that, on input `(K, g, d, n, i)` with
`i < n`, outputs `αᵢ` in the monomial basis `∏ⱼ βⱼ^{eⱼ}` (`0 ≤ eⱼ < deg Pⱼ`) as a list of terms
`(e, coordinates of the coefficient in K)`, for one admissible choice of the `Sⱼ` and points that
works for every choice of roots; `log₂|F|` is `log₂ |K|^{∏ⱼ deg Pⱼ}` (`[F : K] = ∏ⱼ deg Pⱼ` for
pairwise distinct prime degrees). Indices are 0-based. -/
theorem theorem_7_1 :
    ∃ (c : ℕ) (M M₂ : Turing.TM2ComputableAux Bool Bool),
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ g d : ℕ, 1 ≤ g → 1 ≤ d →
      ∃ Pc : List (List (List ℕ)),
        Pc.length = g ∧
        HMBinPacking.OutputsWithin M (encField p f ++ encNat g ++ encNat d)
          (encList (encList (encList encNat)) Pc)
          (c * (g + d + Nat.log 2 (p ^ f.natDegree) + 2) ^ c) ∧
        let P : Fin g → (AdjoinRoot f)[X] := fun j => decPoly p f (Pc.getD j [])
        (∀ j, IsCoeffList p f ((P j).natDegree + 1) (Pc.getD j [])) ∧
        (∀ j, Irreducible (P j)) ∧
        (∀ i j, d ≤ (P i).natDegree ∧ (P i).natDegree ≤ 2 * (P j).natDegree ∧
          2 * (P j).natDegree ≤ c * (d + g) ^ c) ∧
        (∀ j, (P j).natDegree.Prime ∧ (P j).natDegree ≠ p) ∧
        Function.Injective (fun j => (P j).natDegree) ∧
        (∀ n : ℕ, ⌈(n : ℝ) / g⌉₊ ≤ p ^ f.natDegree →
          ∀ (L : Type) [Field L] [Algebra (AdjoinRoot f) L] (β : Fin g → L),
            (∀ j, aeval (β j) (P j) = 0) →
          ∀ S : Fin g → Finset L,
            (∀ j, (↑(S j) : Set L) ⊆ Set.range fun x : AdjoinRoot f => β j + algebraMap _ L x) →
            (∀ j, (S j).card = ⌈(n : ℝ) / g⌉₊) →
          ∀ α : Fin n → IntermediateField.adjoin (AdjoinRoot f) (Set.range β),
            Function.Injective α → (∀ i, (α i : L) ∈ ⋃ j, (↑(S j) : Set L)) →
            Module.finrank (AdjoinRoot f) (IntermediateField.adjoin (AdjoinRoot f) (Set.range β)) ≤
                (d + g) ^ (c * g) ∧
            (∀ i j, i ≠ j → d ≤ (minpoly (AdjoinRoot f) (α i)).natDegree ∧
              (minpoly (AdjoinRoot f) (α i)).natDegree ≤
                2 * (minpoly (AdjoinRoot f) (α j)).natDegree) ∧
            (∀ i j, i ≠ j →
              ∀ τ : IntermediateField.adjoin (AdjoinRoot f) (Set.range β) ≃ₐ[AdjoinRoot f]
                IntermediateField.adjoin (AdjoinRoot f) (Set.range β), τ (α i) ≠ α j) ∧
            ∃ σ : Fin g → (IntermediateField.adjoin (AdjoinRoot f) (Set.range β) ≃ₐ[AdjoinRoot f]
                IntermediateField.adjoin (AdjoinRoot f) (Set.range β)),
              (∀ i x, σ i x =
                x ^ ((p ^ f.natDegree) ^ ((∏ j, (P j).natDegree) / (P i).natDegree))) ∧
              Subgroup.closure (Set.range σ) = ⊤ ∧
              ∀ j, (Finset.univ.filter fun i => σ j (α i) ≠ α i).card ≤ ⌈(n : ℝ) / g⌉₊) ∧
        (∀ n : ℕ, ⌈(n : ℝ) / g⌉₊ ≤ p ^ f.natDegree →
          ∃ αc : List (List (List ℕ × List ℕ)),
            αc.length = n ∧
            (∀ i : ℕ, i < n →
              HMBinPacking.OutputsWithin M₂
                (encField p f ++ encNat g ++ encNat d ++ encNat n ++ encNat i)
                (encList (fun t : List ℕ × List ℕ => encList encNat t.1 ++ encList encNat t.2)
                  (αc.getD i []))
                (c * (Nat.log 2 ((p ^ f.natDegree) ^ ∏ j, (P j).natDegree) + 2) ^ c)) ∧
            (∀ i : ℕ, ∀ t ∈ αc.getD i [], t.1.length = g ∧
              (∀ j : Fin g, t.1.getD j 0 < (P j).natDegree) ∧
              t.2.length = f.natDegree ∧ ∀ a ∈ t.2, a < p) ∧
            ∀ (L : Type) [Field L] [Algebra (AdjoinRoot f) L] (β : Fin g → L),
              (∀ j, aeval (β j) (P j) = 0) →
              let α : Fin n → L := fun i =>
                ((αc.getD i []).map fun t =>
                  decK p f t.2 • ∏ j : Fin g, β j ^ (t.1.getD j 0)).sum
              Function.Injective α ∧
              ∃ S : Fin g → Finset L,
                (∀ j, (↑(S j) : Set L) ⊆ Set.range fun x : AdjoinRoot f => β j + algebraMap _ L x) ∧
                (∀ j, (S j).card = ⌈(n : ℝ) / g⌉₊) ∧ ∀ i, α i ∈ ⋃ j, (↑(S j) : Set L)) := by sorry

end Supplement

end RSSubspaceDesign
