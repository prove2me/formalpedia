-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_5_4
-- name    : RSBeyondJohnson.FirstOrder.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:41.999669+00:00
-- url     : https://prove2.me/theorems/9bc12cdc-5099-4ebc-8a35-95ad5e20f51a
-- title:
--   Lemma 5.4 — degrees of a regular first-order Taylor map
-- statement:
--   Let $D\ge1$, $\ell\ge1$, $\tau=\max\{0,2D-3\}$. Suppose a first-order equation $Q\in F[X,Z,Y_0,Y_1]$ has total jet degree at most $j$, $Y_1$-degree at most $r$ with $1\le r\le j$, and challenge degree at most $H$. Fix a Taylor center $x_0\in F$, put $Q_{x_0}=Q(x_0,Z,Y_0,Y_1)$ and $q=(\partial Q/\partial Y_1)(x_0,Z,Y_0,Y_1)$, and assume characteristic zero or $p>D$. Then on $V(Q_{x_0})$ where $q$ is nonzero, Taylor reconstruction through message degree $D$, with the coordinates $(Z,Z^2,\dots,Z^\ell,P)$ retained, is given by numerators and a common denominator in $F[Z,Y_0,Y_1]$ of degrees at most
--   $$b=1+\tau(j-1),\qquad c=\min\{b,\tau(r-1)+D\},\qquad D_Z=\ell+\tau H\qquad(42)$$
--   in total jet degree, $Y_1$-degree and challenge degree respectively; the denominator does not vanish where $q\ne0$.
--
--   Differences from the source:
--   - encoding: Taylor reconstruction through message degree D → taylorMap (definition Taylor): Kopparty's recurrence c_s = −[T^{s−1}]Q(x₀+T, z, Σ_{j<s} c_jT^j, Σ j c_jT^{j−1})/(s q), P = Σ_{s≤D} c_s (X − x₀)^s, with (z, …, z^ℓ) prepended; reason: the recurrence of §5.2 (p. 31), evaluated pointwise
--   - reading: on every component of V(Q_{x₀}) where q is nonzero, the map has numerator and common-denominator degrees at most (b, c, D_Z) → ∃ numerators and one denominator in F[Z, Y₀, Y₁] with these degree bounds such that at every point (z, c₀, c₁) over any extension K of F with Q_{x₀} = 0 and q ≠ 0 the denominator is nonzero and the map equals numerators/denominator; reason: a rational map on those components is determined by its values where it is defined; q ≠ 0 is where the recurrence is defined
--   - encoding: Q ∈ F[X, Z, Y₀, Y₁] and its degrees → (MvPolynomial (Option (Fin 2)) F)[X]; jetDegree, degreeOf (some 1) of every Z-coefficient; natDegree; reason: same quantities
--   - encoding: τ = max{0, 2D − 3}, j − 1, r − 1 → natural subtraction; reason: 2D − 3 truncates exactly to the max with 0; j, r ≥ 1
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 32, Lemma 5.4

import Mathlib
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation
import Definitions.Def_RSBeyondJohnson_FirstOrder_Taylor

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 5.4 (Degrees of a regular first-order Taylor map)**, p. 32. Let `D ≥ 1`, `ℓ ≥ 1`,
`τ = max{0, 2D − 3}`, and let `Q ∈ F[X, Z, Y₀, Y₁]` have total jet degree `≤ j`, `Y₁`-degree
`≤ r` with `1 ≤ r ≤ j`, and challenge degree `≤ H`; fix `x₀ ∈ F`; assume characteristic zero or
`p > D`. Then Taylor reconstruction through message degree `D` with the coordinates
`(Z, Z², …, Z^ℓ, P)` retained is a rational map given by numerators and a common denominator in
`F[Z, Y₀, Y₁]` (`Fin 3`: `0 = Z`, `1 = Y₀`, `2 = Y₁`) of total jet degree `≤ b = 1 + τ(j − 1)`,
`Y₁`-degree `≤ c = min{b, τ(r − 1) + D}` and challenge degree `≤ D_Z = ℓ + τH` (42): at every point
`(z, c₀, c₁)` of `V(Q_{x₀})` (over any extension `K` of `F`) where `q = (∂Q/∂Y₁)(x₀, ·)` is
nonzero, the denominator is nonzero and the map equals numerators over denominator. -/
theorem lemma_5_4.{u} {F : Type u} [Field F] (D ℓ j r H : ℕ) (hD : 1 ≤ D) (hℓ : 1 ≤ ℓ)
    (Q : (MvPolynomial (Option (Fin 2)) F)[X])
    (hjet : ∀ i, jetDegree (Q.coeff i) ≤ j) (hr1 : 1 ≤ r) (hrj : r ≤ j)
    (hr : ∀ i, (Q.coeff i).degreeOf (some 1) ≤ r) (hH : Q.natDegree ≤ H) (x₀ : F)
    (hchar : ringChar F = 0 ∨ D < ringChar F) :
    ∃ (Num : Fin (ℓ + (D + 1)) → MvPolynomial (Fin 3) F) (Den : MvPolynomial (Fin 3) F),
      (∀ i, (Num i).weightedTotalDegree (fun v : Fin 3 => if v = 0 then 0 else 1) ≤
          1 + max 0 (2 * D - 3) * (j - 1) ∧
        (Num i).degreeOf 2 ≤ min (1 + max 0 (2 * D - 3) * (j - 1)) (max 0 (2 * D - 3) * (r - 1) + D) ∧
        (Num i).degreeOf 0 ≤ ℓ + max 0 (2 * D - 3) * H) ∧
      (Den.weightedTotalDegree (fun v : Fin 3 => if v = 0 then 0 else 1) ≤
          1 + max 0 (2 * D - 3) * (j - 1) ∧
        Den.degreeOf 2 ≤ min (1 + max 0 (2 * D - 3) * (j - 1)) (max 0 (2 * D - 3) * (r - 1) + D) ∧
        Den.degreeOf 0 ≤ ℓ + max 0 (2 * D - 3) * H) ∧
      ∀ (K : Type u) [Field K] [Algebra F K] (z c₀ c₁ : K),
        evalAt Q x₀ z c₀ c₁ = 0 → separantAt Q x₀ z c₀ c₁ ≠ 0 →
          MvPolynomial.aeval ![z, c₀, c₁] Den ≠ 0 ∧
          ∀ i, taylorMap Q x₀ ℓ D z c₀ c₁ i =
            MvPolynomial.aeval ![z, c₀, c₁] (Num i) / MvPolynomial.aeval ![z, c₀, c₁] Den := by sorry

end RSBeyondJohnson.FirstOrder
