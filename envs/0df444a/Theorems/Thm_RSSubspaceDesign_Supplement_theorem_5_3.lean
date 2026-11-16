-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_5_3
-- name    : RSSubspaceDesign.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:42:35.323627+00:00
-- url     : https://prove2.me/theorems/c2dd2eac-457c-4227-aa95-4676dd333686
-- title:
--   Theorem 5.3 — pruning a $\le d$-dimensional $K(X)$-space: all messages with $\ge k+\varepsilon n$ agreements, list $(O(1/\varepsilon))^d$, time $O_{d,\varepsilon}(1)\,\mathrm{poly}(n,\log|F|)$
-- statement:
--   For every integer $d \ge 1$ and every $0 < \varepsilon < 1/2$ there is a constant $C(d,\varepsilon) = \exp\bigl(O(d^3\log(1/\varepsilon))\bigr)$ with the following property. Let $K \subseteq F$ be finite fields and consider a Reed–Solomon code over $F$ of length $n$ and dimension $k$, with $n$ sufficiently large in terms of $d$ and $\varepsilon$. Suppose its evaluation points $\alpha_1, \dots, \alpha_n \in F$ are pairwise nonconjugate over $K$ and satisfy
--   $$
--   C(d,\varepsilon) \le \deg_K \alpha_i \le 2\deg_K \alpha_j \qquad (1 \le i, j \le n),
--   $$
--   where $\deg_K \alpha = [K(\alpha):K]$. Suppose also that we are given the evaluation points, a received word $y \in F^n$, and a $K(X)$-linear space $A \subseteq F(X)$ of dimension at most $d$, by a $K(X)$-basis of polynomials in $F[X]_{<k}$. Then one can output all polynomials $f \in A \cap F[X]$ of degree less than $k$ with
--   $$
--   |\{j : f(\alpha_j) = y_j\}| \ge k + \varepsilon n .
--   $$
--   The list has size at most $(O(1/\varepsilon))^d$ and is computed in time $O_{d,\varepsilon}(1)\cdot\mathrm{poly}(n, \log|F|)$.
--
--   This is the second step of the decoder of Theorem 5.1, the pruning step of Section 6.
--
--   **Formalization Note** Encodings as in Theorem 5.1. The basis is a list of at most $d$ polynomials of $F[X]_{<k}$, linearly independent over $K(X)$ in $F(X)$ (the published `ratFuncAlgebra`), and $A$ is its span. $C(d,\varepsilon)$ is a real number at most $\exp(c_0 d^3\ln(1/\varepsilon))$ with $c_0$ absolute. The machine, the threshold for $n$ and the multiplier of $O_{d,\varepsilon}(1)$ depend on $d$ and $\varepsilon$. The exponent of $\mathrm{poly}$ and the constant of $(c/\varepsilon)^d$ are absolute. The output lists each polynomial once and is exactly the set above.
--
--   Differences from the source:
--   - encoding: finite fields K ⊆ F; the evaluation points, the generators σ_ℓ of Gal(F/K) and y as given objects → K = 𝔽_p[Y]/(f), F = K[X]/(h) with h monic irreducible; points, y and output coefficients in the power basis of F/K; σ_ℓ input as an exponent e_ℓ < deg h with σ_ℓ(x) = x^{|K|^{e_ℓ}}; one Turing machine with an explicit step bound; reason: every finite extension is isomorphic to such a K[X]/(h) and every element of Gal(F/K) is a power of x ↦ x^{|K|}; the base mission's machine model
--   - reading: "one can output all polynomials …" for the given code → one machine per (d, ε), uniform over K, F, n, k, y and the basis; reason: an algorithm per instance would empty the time clause; the paper's algorithm is uniform
--   - encoding: C(d, ε) = exp(O(d³ log(1/ε))); (O(1/ε))^d; poly(n, log|F|) → a real C(d, ε) ≤ exp(c₀ d³ ln(1/ε)); (c/ε)^d; (n + ⌊log₂|F|⌋ + 2)^c, with c₀, c absolute; reason: the paper's O-conventions written out
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 5.3, p.23 (PDF 25), restated p.25 (PDF 27)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 5.3 (Pruning a low-dimensional `K(X)`-space).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 5.3, p.23 (restated p.25).

For every integer `d ≥ 1` and every `0 < ε < 1/2`, there is a constant
`C(d, ε) = exp(O(d³ log(1/ε)))` with the following property. Let `K ⊆ F` be finite fields, and
consider a Reed–Solomon code of length `n` and dimension `k` over `F`, where `n` is sufficiently large
in terms of `d` and `ε`. Suppose its evaluation points `α₁, …, αₙ ∈ F` are pairwise nonconjugate over
`K` and satisfy `C(d, ε) ≤ deg_K αᵢ ≤ 2 deg_K αⱼ` (`1 ≤ i, j ≤ n`). Given the evaluation points, a
received word `y ∈ Fⁿ`, and a `K(X)`-linear space `A ⊆ F(X)` of dimension at most `d`, given by a basis
over `K(X)` consisting of polynomials in `F[X]_{<k}`, one can output all polynomials `f ∈ A ∩ F[X]` of
degree less than `k` satisfying `|{j : f(αⱼ) = yⱼ}| ≥ k + εn`. The list has size at most
`(O(1/ε))^d`, and can be computed in time `O_{d,ε}(1) poly(n, log |F|)`.

**Formalization Note.** Encodings as in `theorem_5_1`. The basis is a list of at most `d`
polynomials of `F[X]_{<k}` (each by its `k` coefficients), linearly independent over `K(X)` in `F(X)`
(published `ratFuncAlgebra`); `A` is its `K(X)`-span and "`f ∈ A ∩ F[X]`" is: the image of `f` in
`F(X)` lies in `A`. `C(d, ε)` is a real number with `C(d, ε) ≤ exp(c₀ d³ ln(1/ε))`, `c₀` absolute.
`M`, `N` and the multiplier `B` of `O_{d,ε}(1)` are chosen after `d, ε`; `c` (in `poly` and in
`(O(1/ε))^d = (c/ε)^d`) is absolute. The output lists the polynomials without repetition, exactly. -/
theorem theorem_5_3 :
    ∃ c₀ c : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ Cdε : ℝ, Cdε ≤ Real.exp (c₀ * (d : ℝ) ^ 3 * Real.log (1 / ε)) ∧
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (N B : ℕ),
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
      (∀ i j : Fin n, Cdε ≤ ((minpoly (AdjoinRoot f) (α i)).natDegree : ℝ) ∧
        (minpoly (AdjoinRoot f) (α i)).natDegree ≤ 2 * (minpoly (AdjoinRoot f) (α j)).natDegree) →
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ yc : List (List (List ℕ)), yc.length = n →
        (∀ x ∈ yc, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let y : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun j => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (yc.getD j []))
      let decM : List (List (List ℕ)) → (AdjoinRoot (decPoly p f hc))[X] :=
        fun m => ∑ i : Fin m.length,
          C (AdjoinRoot.mk (decPoly p f hc) (decPoly p f (m.get i))) * X ^ (i : ℕ)
      ∀ bs : List (List (List (List ℕ))),
        (∀ b ∈ bs, b.length = k ∧ ∀ x ∈ b, IsCoeffList p f (decPoly p f hc).natDegree x) →
        bs.length ≤ d →
      letI := ratFuncAlgebra (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))
      LinearIndependent (RatFunc (AdjoinRoot f))
          (fun i : Fin bs.length =>
            algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc)))
              (decM (bs.get i))) →
      ∃ out : List (List (List (List ℕ))),
        (∀ m ∈ out, m.length = k ∧ ∀ x ∈ m, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
        HMBinPacking.OutputsWithin M
          (encField p f ++ encNat n ++ encNat k ++ encList (encList encNat) hc ++
                encList (encList (encList encNat)) ac ++
            encList (encList (encList encNat)) yc ++
            encList (encList (encList (encList encNat))) bs)
          (encList (encList (encList (encList encNat))) out)
          (B * (n + Nat.log 2 ((p ^ f.natDegree) ^ (decPoly p f hc).natDegree) + 2) ^ c) ∧
        (out.map decM).Nodup ∧
        (∀ P : (AdjoinRoot (decPoly p f hc))[X], P ∈ out.map decM ↔
          (P ∈ degreeLT (AdjoinRoot (decPoly p f hc)) k ∧
            algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc))) P ∈
              Submodule.span (RatFunc (AdjoinRoot f))
                (Set.range fun i : Fin bs.length =>
                  algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc)))
                    (decM (bs.get i))) ∧
            (k : ℝ) + ε * n ≤ ((Finset.univ.filter fun j => P.eval (α j) = y j).card : ℝ))) ∧
        (out.length : ℝ) ≤ ((c : ℝ) / ε) ^ d := by sorry

end Supplement

end RSSubspaceDesign
