-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_5_1
-- name    : RSSubspaceDesign.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:41:28.347534+00:00
-- url     : https://prove2.me/theorems/8f6ef202-8c28-4322-8dbc-01b1e44405d5
-- title:
--   Theorem 5.1 — list decoding to agreement $k+\varepsilon n$: list $(1/\varepsilon)^{O(1/\varepsilon)}$, time $O_{g,\varepsilon}(1)\,\mathrm{poly}(n,\log|F|)$
-- statement:
--   For every $0 < \varepsilon < 1/2$ there is a constant $C(\varepsilon) = \exp\bigl(O(\varepsilon^{-3}\log(1/\varepsilon))\bigr)$ with the following property. Let $K \subseteq F$ be finite fields and $\alpha_1, \dots, \alpha_n \in F$, with $n$ sufficiently large in terms of $\varepsilon$; write $\deg_K \alpha = [K(\alpha) : K]$. Suppose:
--
--   1. the points $\alpha_1, \dots, \alpha_n$ are pairwise nonconjugate over $K$;
--   2. there are an integer $g \ge 1$ with $g \ge 12\log_2(1/\varepsilon)/\varepsilon$ and generators $\sigma_1, \dots, \sigma_g$ of $\mathrm{Gal}(F/K)$ with $|\{j : \sigma_\ell(\alpha_j) \neq \alpha_j\}| \le \lceil n/g \rceil$ for every $\ell$;
--   3. $C(\varepsilon) \le \deg_K \alpha_i \le 2\deg_K \alpha_j$ for all $i, j$.
--
--   Then for every $1 \le k \le n$ there is a deterministic algorithm with the following input and output. It is given the points, the generators and a received word $y \in F^n$. It outputs all $f \in F[X]_{<k}$ with
--   $$
--   |\{j : f(\alpha_j) \neq y_j\}| \le n - k - \varepsilon n .
--   $$
--   The output list has size at most $(1/\varepsilon)^{O(1/\varepsilon)}$, and the algorithm runs in time $O_{g,\varepsilon}(1)\cdot\mathrm{poly}(n, \log|F|)$.
--
--   This is the list-decoding engine behind Theorems 1.1–1.3. Condition 2 is used to find a low-dimensional space of candidates (Theorem 5.2), condition 3 to prune it (Theorem 5.3).
--
--   **Formalization Note** $K = \mathbb F_p[Y]/(f)$ and $F = K[X]/(h)$ for a monic irreducible $h$. Elements are written in the power basis of $F/K$. A generator is given by an exponent $e_\ell < \deg h$ with $\sigma_\ell(x) = x^{|K|^{e_\ell}}$. The output is a repetition-free list of the messages, each by its $k$ coefficients, equal to the set above. $C(\varepsilon)$ is a real number at most $\exp(c_0\varepsilon^{-3}\ln(1/\varepsilon))$, with $c_0$ absolute. The machine and the threshold for $n$ depend on $\varepsilon$, and the multiplier of $O_{g,\varepsilon}(1)$ on $g$ and $\varepsilon$. The exponent of $\mathrm{poly}$ and the constant in $(1/\varepsilon)^{c/\varepsilon}$ are absolute.
--
--   Differences from the source:
--   - encoding: finite fields K ⊆ F; the evaluation points, the generators σ_ℓ of Gal(F/K) and y as given objects → K = 𝔽_p[Y]/(f), F = K[X]/(h) with h monic irreducible; points, y and output coefficients in the power basis of F/K; σ_ℓ input as an exponent e_ℓ < deg h with σ_ℓ(x) = x^{|K|^{e_ℓ}}; one Turing machine with an explicit step bound; reason: every finite extension is isomorphic to such a K[X]/(h) and every element of Gal(F/K) is a power of x ↦ x^{|K|}; the base mission's machine model
--   - reading: "admits a deterministic list-decoding algorithm" (for each code) → one machine per ε, reading the points, the generators and y, uniform over K, F, n, g and k; time multiplier B chosen after g and ε; reason: an algorithm chosen after the code could be a lookup table, which empties the time clause; the paper's algorithm is uniform
--   - encoding: C(ε) = exp(O(ε⁻³ log(1/ε))); (1/ε)^{O(1/ε)}; poly(n, log|F|) → a real C(ε) ≤ exp(c₀ ε⁻³ ln(1/ε)); (1/ε)^{c/ε}; (n + ⌊log₂|F|⌋ + 2)^c, with c₀, c absolute; reason: the paper's O-conventions written out; the base of the logarithm only changes c₀
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 5.1, p.22 (PDF 24)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 5.1 (List decoding near capacity).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215
(held version, sha256 cf26424b…f36206), Theorem 5.1, p.22.

For every `0 < ε < 1/2`, there exists a constant `C(ε) = exp(O(ε⁻³ log(1/ε)))` with the following
property. Let `K ⊆ F` be finite fields, and let `α₁, …, αₙ ∈ F`, where `n` is sufficiently large in
terms of `ε`. Write `deg_K α = [K(α) : K]`. Suppose that
1. the points `α₁, …, αₙ` are pairwise nonconjugate over `K`;
2. there is a positive integer `g ≥ 12 log₂(1/ε)/ε` and a generating set `σ₁, …, σ_g` of
   `Gal(F/K)` such that, for every `1 ≤ ℓ ≤ g`, `|{j : σ_ℓ(αⱼ) ≠ αⱼ}| ≤ ⌈n/g⌉`;
3. for every `1 ≤ i, j ≤ n`, `C(ε) ≤ deg_K αᵢ ≤ 2 deg_K αⱼ`.
Then, for every integer `1 ≤ k ≤ n`, `RS_F((α₁, …, αₙ), k)` admits a deterministic list-decoding
algorithm: given the evaluation points, the generators, and a received word `y ∈ Fⁿ`, it outputs all
`f ∈ F[X]_{<k}` with `|{j : f(αⱼ) ≠ yⱼ}| ≤ n − k − εn`. The output list has size at most
`(1/ε)^{O(1/ε)}`, and the algorithm runs in time `O_{g,ε}(1) poly(n, log |F|)`.

**Formalization Note.** `K` is input as `p, f` (`K = AdjoinRoot f`) and `F` as a monic irreducible
`h ∈ K[X]` (`F = K[X]/(h)`, `|F| = |K|^{deg h}`); every finite extension is isomorphic to one of these.
Points, `y` and output coefficients are written in the power basis of `F/K` and decoded
structurally. A generator `σ_ℓ ∈ Gal(F/K)` is input as an exponent `e_ℓ < deg h` with
`σ_ℓ(x) = x^{|K|^{e_ℓ}}` (every element of `Gal(F/K)` has this form). Non-conjugate: no
`K`-automorphism maps `αᵢ` to `αⱼ` (`i ≠ j`). `deg_K α` is the degree of the minimal polynomial.
`C(ε)` is a real number with `C(ε) ≤ exp(c₀ ε⁻³ ln(1/ε))` for an absolute `c₀` (the `O` hides a
constant; the base of the logarithm only changes it). One machine `M` and threshold `N` per `ε`;
the multiplier `B` of `O_{g,ε}(1)` is chosen after `g`; `c` (in `poly` and in
`(1/ε)^{O(1/ε)} = (1/ε)^{c/ε}`) is absolute. The output is the list of messages, each as its `k`
coefficients, without repetition and exactly the polynomials described. Indices are 0-based. -/
theorem theorem_5_1 :
    ∃ c₀ c : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ Cε : ℝ, Cε ≤ Real.exp (c₀ * (1 / ε ^ 3) * Real.log (1 / ε)) ∧
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (N : ℕ), ∀ g : ℕ, ∃ B : ℕ,
      ∀ n : ℕ, N ≤ n →
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ hc : List (List ℕ), IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc →
        (decPoly p f hc).Monic → ∀ hirr : Irreducible (decPoly p f hc),
      haveI : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
      ∀ ac : List (List (List ℕ)), ac.length = n →
        (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let α : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun i => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i []))
      (∀ i j : Fin n, i ≠ j → ∀ τ : AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f]
          AdjoinRoot (decPoly p f hc), τ (α i) ≠ α j) →
      1 ≤ g → 12 * Real.logb 2 (1 / ε) / ε ≤ g →
      ∀ e : Fin g → ℕ, (∀ l, e l < (decPoly p f hc).natDegree) →
      ∀ σ : Fin g → (AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f] AdjoinRoot (decPoly p f hc)),
        (∀ l x, σ l x = x ^ ((p ^ f.natDegree) ^ e l)) →
        Subgroup.closure (Set.range σ) = ⊤ →
        (∀ l, (Finset.univ.filter fun j => σ l (α j) ≠ α j).card ≤ ⌈(n : ℝ) / g⌉₊) →
      (∀ i j : Fin n, Cε ≤ ((minpoly (AdjoinRoot f) (α i)).natDegree : ℝ) ∧
        (minpoly (AdjoinRoot f) (α i)).natDegree ≤ 2 * (minpoly (AdjoinRoot f) (α j)).natDegree) →
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ yc : List (List (List ℕ)), yc.length = n →
        (∀ x ∈ yc, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let y : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun j => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (yc.getD j []))
      let decM : List (List (List ℕ)) → (AdjoinRoot (decPoly p f hc))[X] :=
        fun m => ∑ i : Fin m.length,
          C (AdjoinRoot.mk (decPoly p f hc) (decPoly p f (m.get i))) * X ^ (i : ℕ)
      ∃ out : List (List (List (List ℕ))),
        (∀ m ∈ out, m.length = k ∧ ∀ x ∈ m, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
        HMBinPacking.OutputsWithin M
          (encField p f ++ encNat n ++ encNat k ++ encList (encList encNat) hc ++
                encList (encList (encList encNat)) ac ++
            encList encNat (List.ofFn e) ++ encList (encList (encList encNat)) yc)
          (encList (encList (encList (encList encNat))) out)
          (B * (n + Nat.log 2 ((p ^ f.natDegree) ^ (decPoly p f hc).natDegree) + 2) ^ c) ∧
        (out.map decM).Nodup ∧
        (∀ P : (AdjoinRoot (decPoly p f hc))[X], P ∈ out.map decM ↔
          (P ∈ degreeLT (AdjoinRoot (decPoly p f hc)) k ∧
            ((Finset.univ.filter fun j => P.eval (α j) ≠ y j).card : ℝ) ≤ n - k - ε * n)) ∧
        (out.length : ℝ) ≤ (1 / ε) ^ ((c : ℝ) / ε) := by sorry

end Supplement

end RSSubspaceDesign
