-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_two_chart_analytic_inputs
-- name    : WeierstrassEllipticZeta.two_chart_analytic_inputs
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T20:24:25.658157+00:00
-- url     : https://prove2.me/theorems/1bc0d856-73a7-43c3-affd-94e3888eba1c
-- title:
--   Two affine charts supply the analytic multiplicity inputs
-- statement:
--   Let the five complex functions $S_j$ be entire and satisfy
--
--   $$S_0S_4-S_2S_3-2S_1^2=0.$$
--
--   Let $Q$ be a polynomial in seven variables, homogeneous of degree $n$ in its last five variables, and set
--
--   $$F(z)=Q(1,z,S_0(z),S_1(z),S_2(z),S_3(z),S_4(z)).$$
--
--   For either of the two affine charts, whose denominators are $S_0$ and $S_2$, let $f_c$ be the evaluation of the corresponding normalized four-variable polynomial along the chart coordinates. Fix an arbitrary set $Y\subseteq\mathbb C$ and an integer $T\ge0$.
--
--   Assume that $f_c$ has finite analytic order at at least one point where its chart denominator is nonzero. Assume also that at every point of $Y$, at least one valid affine chart has analytic order at least $T$.
--
--   Then $F$ is not identically zero, and every projective normalization with nonzero denominator at a point of $Y$ has analytic order at least $T$ there:
--
--   $$\operatorname{ord}_z Q(1,w,S_0(w)/S_j(w),\ldots,S_4(w)/S_j(w))\ge T
--   \quad(z\in Y,\ S_j(z)\ne0).$$
--
--   Only homogeneity in the last five variables is required. No multiplicity estimate, degree bound, finite enumeration of $Y$, or algebraic-group identification is assumed or concluded. The result supplies the analytic inputs needed to connect the older contact-ideal formulation of A.1 to its existing analytic obstruction formulation.
-- source:
--   Derived two-chart analytic-input transfer for Senthil Kumar K (2026), Appendix A.2, the projective coordinate display preceding Lemma A.1, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The proof uses the already-Proved homogeneous chart-order theorem https://prove2.me/theorems/952dcffd-fccc-48eb-99d8-6258e3e0ed6e and the quadratic coordinate relation. Pinned analytic germ facts: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Order.lean. The transfer is derived here, not quoted as a theorem of the paper. Its application connects the existing rank obstruction https://prove2.me/theorems/9437b1f5-e3d8-4b4f-bca2-d8104aa8218d to the existing linear analytic obstruction https://prove2.me/theorems/9acd36b2-ab77-4168-8242-cb12676662c4, using the Proved subgroup profile https://prove2.me/theorems/99c6c72e-8d6f-48fb-8904-ae800f4a5cbc. The constant C is preserved, no new Open theorem is introduced, and the global geometric cost comparison and integer-search bound are not improved.

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta MvPolynomial
open scoped Classical

theorem WeierstrassEllipticZeta.two_chart_analytic_inputs
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hquad : ∀ z, S 0 z * S 4 z - S 2 z * S 3 z - 2 * S 1 z ^ 2 = 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n T : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (Y : Set ℂ)
    (hfinite : ∃ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 ∧
      analyticOrderAt (fun w => eval (extensionChartCoordinates S c w)
        (extensionChartNormalize c Q)) z ≠ ⊤)
    (hhigh : ∀ z ∈ Y, ∃ c : Fin 2, S (extensionChartDenominator c) z ≠ 0 ∧
      (T : ℕ∞) ≤ analyticOrderAt (fun w => eval (extensionChartCoordinates S c w)
        (extensionChartNormalize c Q)) z) :
    (fun z : ℂ => eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 ∧
      ∀ z ∈ Y, ∀ j : Fin 5, S j z ≠ 0 →
        (T : ℕ∞) ≤ analyticOrderAt (fun w => eval
          ![1, w, S 0 w / S j w, S 1 w / S j w, S 2 w / S j w,
            S 3 w / S j w, S 4 w / S j w] Q) z := by sorry
