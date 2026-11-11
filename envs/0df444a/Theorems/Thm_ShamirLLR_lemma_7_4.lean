-- Prove2me | Theorems.Thm_ShamirLLR_lemma_7_4
-- name    : ShamirLLR.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:49.390604+00:00
-- url     : https://prove2.me/theorems/46d900f0-ab3c-4fc4-877b-d23ad2d630d2
-- title:
--   Lemma 7.4 — positive approximation on a torus
-- statement:
--   Fix $0\le d_H\le D$ with $D\ge1$. For $Q_0\ge1$, a $Q_0$-Lipschitz probability function $A:\mathbb T^{d_H}\to[0,1]$ and $0<\varepsilon<1$, the positive product Fejér convolution $A_T$ is a trigonometric polynomial $A_T:\mathbb T^{d_H}\to[0,1]$ with
--   $$
--   \|A-A_T\|_\infty\le\varepsilon,\qquad \mathrm{supp}\,\widehat{A_T}\subseteq[-T,T]^{d_H}\cap\mathbb Z^{d_H},
--   $$
--   for some integer $T\le1+(2DQ_0/\varepsilon)^2$; it sends $1-A$ to $1-A_T$, and every larger integer $T\ge(2DQ_0/\varepsilon)^2$ retains the discrepancy, range, complement and Fourier-support conclusions.
--
--   This supplies finite Fourier models that keep the range $[0,1]$, so complements and positivity survive the approximation.
--
--   Differences from the source:
--   - generalization: $A$ $Q_0$-Lipschitz for the usual product torus metric → $|A(x)-A(y)|\le Q_0\sum_j\|x_j-y_j\|_{\mathbb T}$ (the $\ell^1$ distance); reason: the proof bounds the discrepancy by $Q_0\sum_j\int\|t_j\|K_T(t_j)dt_j$; a sup-metric Lipschitz function satisfies the $\ell^1$ bound with the same $Q_0$
--   - reading: "positive product Fejér convolution gives … $A_T$", "Larger $T$ retain …" → $A_T$ is `fejerMean T A`, for every integer $T\ge1$ with $T\ge(2DQ_0/\varepsilon)^2$, plus the existence of such $T\le1+(2DQ_0/\varepsilon)^2$; reason: the construction of the proof, $T=\lceil(2DQ_0/\varepsilon)^2\rceil$
--   - encoding: trigonometric polynomial → continuous function with torus Fourier coefficients vanishing outside $[-T,T]^{d_H}$; reason: a continuous function with finite Fourier support is a trigonometric polynomial
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 7.4, p.53, and proof, pp.53–54 (PDF pp.54–55)

import Mathlib
import Definitions.Def_ShamirLLR_torus

set_option autoImplicit false

namespace ShamirLLR

/-- **Lemma 7.4 (Positive Approximation on a Torus).** Fix `0 ≤ d_H ≤ D`. For `Q₀ ≥ 1`, a
`Q₀`-Lipschitz probability function `A : 𝕋^{d_H} → [0, 1]` and `0 < ε < 1`, the positive product
Fejér convolution `A_T` is a trigonometric polynomial with values in `[0, 1]`,
`‖A − A_T‖_∞ ≤ ε`, `supp Â_T ⊆ [−T, T]^{d_H} ∩ ℤ^{d_H}`, for some `T ≤ 1 + (2DQ₀/ε)²`; it sends
`1 − A` to `1 − A_T`, and larger `T` retain the discrepancy, range, complement and
Fourier-support conclusions.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 7.4, p.53, and its proof, pp.53–54.

**Formalization Note.** "Larger T" is the clause for every integer `T ≥ max(1, (2DQ₀/ε)²)`; the
existence of such a `T ≤ 1 + (2DQ₀/ε)²` is the second clause. `Q₀`-Lipschitz is assumed for the
`ℓ¹` torus distance `∑_j ‖x_j − y_j‖_𝕋`, the bound the proof uses; it is implied by the
sup-metric Lipschitz condition with the same `Q₀`. Continuity of `A_T` with finite Fourier
support makes it a trigonometric polynomial. -/
theorem lemma_7_4 (D : ℕ) (hD : 1 ≤ D) (dH : ℕ) (hdH : dH ≤ D) (Q₀ : ℝ) (hQ₀ : 1 ≤ Q₀)
    (A : Torus dH → ℝ) (hA : ∀ t, 0 ≤ A t ∧ A t ≤ 1)
    (hLip : ∀ x y, |A x - A y| ≤ Q₀ * l1dist x y) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∀ T : ℕ, 1 ≤ T → (2 * D * Q₀ / ε) ^ 2 ≤ T →
        Continuous (fejerMean T A) ∧ (∀ x, 0 ≤ fejerMean T A x ∧ fejerMean T A x ≤ 1) ∧
        (∀ x, |A x - fejerMean T A x| ≤ ε) ∧ FourierSuppIn (fejerMean T A) T ∧
        fejerMean T (fun t => 1 - A t) = fun x => 1 - fejerMean T A x) ∧
      ∃ T : ℕ, 1 ≤ T ∧ (2 * D * Q₀ / ε) ^ 2 ≤ T ∧ (T : ℝ) ≤ 1 + (2 * D * Q₀ / ε) ^ 2 := by sorry

end ShamirLLR
