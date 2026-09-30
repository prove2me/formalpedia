-- Prove2me | Theorems.Thm_TranscendenceTheory_projective_chart_vanishing_order
-- name    : TranscendenceTheory.projective_chart_vanishing_order
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T15:06:41.788506+00:00
-- url     : https://prove2.me/theorems/952dcffd-fccc-48eb-99d8-6258e3e0ed6e
-- title:
--   Vanishing order is preserved by projective chart normalization
-- statement:
--   Let $A_0,A_1,S_0,\ldots,S_4:\mathbb C\to\mathbb C$ be analytic at $z$. Let $Q$ be a complex polynomial in the seven variables $Y_0,Y_1,X_0,\ldots,X_4$, homogeneous of degree $n\ge0$ in the last five variables: every monomial with nonzero coefficient has total $X$ degree $n$. There is no homogeneity or degree requirement on the first two variables. Choose $j\in\{0,\ldots,4\}$ with $S_j(z)\ne0$ and define
--
--   $$F(w)=Q\big(A_0(w),A_1(w);S_0(w),\ldots,S_4(w)\big),$$
--
--   $$F_j(w)=Q\left(A_0(w),A_1(w);\frac{S_0(w)}{S_j(w)},\ldots,\frac{S_4(w)}{S_j(w)}\right).$$
--
--   Both functions are analytic at $z$, and
--
--   $$\operatorname{ord}_z F=\operatorname{ord}_z F_j.$$
--
--   Here the order is an extended natural number, with value $\infty$ when the analytic germ is zero. Furthermore, for every integer $T\ge0$,
--
--   $$\operatorname{ord}_z F_j\le T\quad\Longleftrightarrow\quad
--   \exists k\in\{0,\ldots,T\}\ \ F^{(k)}(z)\ne0.$$
--
--   Only local analyticity is required, and the chosen coordinate need only be nonzero at the specified point. The zero polynomial, degree zero and infinite vanishing order are included. The conclusion identifies the multiplicity in any valid projective chart with that of the original homogeneous lift.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and equations (A.8)-(A.9), https://doi.org/10.1017/S001309152610145X. This derived general analytic lemma justifies the passage between the homogeneous lift and local projective vanishing order. It is proved directly from monomial homogeneity and analytic order under multiplication by a unit, for arbitrary local analytic coordinate functions; it asserts no elliptic zero estimate.

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

theorem TranscendenceTheory.projective_chart_vanishing_order
    (A : Fin 2 → ℂ → ℂ) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (z : ℂ) (j : Fin 5) (hj : S j z ≠ 0)
    (hA : ∀ i, AnalyticAt ℂ (A i) z) (hS : ∀ i, AnalyticAt ℂ (S i) z) :
    let F : ℂ → ℂ := fun w => MvPolynomial.eval
      ![A 0 w, A 1 w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q
    let Fⱼ : ℂ → ℂ := fun w => MvPolynomial.eval
      ![A 0 w, A 1 w, S 0 w / S j w, S 1 w / S j w,
        S 2 w / S j w, S 3 w / S j w, S 4 w / S j w] Q
    AnalyticAt ℂ F z ∧ AnalyticAt ℂ Fⱼ z ∧
      analyticOrderAt F z = analyticOrderAt Fⱼ z ∧
      ∀ T : ℕ, analyticOrderAt Fⱼ z ≤ T ↔
        ∃ k : ℕ, k ≤ T ∧ iteratedDeriv k F z ≠ 0 := by sorry
