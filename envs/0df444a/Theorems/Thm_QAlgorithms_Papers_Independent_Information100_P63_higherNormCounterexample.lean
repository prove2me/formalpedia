-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_higherNormCounterexample
-- name    : QAlgorithms.Papers.Independent.Information100.P63.higherNormCounterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:44:38.796029+00:00
-- url     : https://prove2.me/theorems/113133a7-54d8-4e44-962b-0c4ed72ac475
-- title:
--   Explicit counterexample for higher Schatten exponents
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   Define $X=\operatorname{diag}(42,29,29)/100$ and $Y=\operatorname{diag}(40,35,25)/100$. These are states. For every $t>0$,
--
--   $$
--   \det(tI+X)-\det(tI+Y)=\frac{t}{5000}+\frac{161}{500000}>0,\qquad L_t(X)>L_t(Y).
--   $$
--
--   Nevertheless,
--
--   $$
--   \operatorname{Tr}X^3=\frac{61433}{500000}>\frac{49}{400}=\operatorname{Tr}Y^3,\qquad\|X\|_3>\|Y\|_3,\qquad\delta_{\rm maj}(X,Y)=\frac1{50}.
--   $$
--
--   The fixed pair shows failure of the higher-norm extension and, as constant sequences, failure of vanishing defect from log-determinant ordering alone.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 14, Appendix A.1, Eqs. (75)–(77); p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A.1, Eqs.(75)–(77), PDF p.14, and the constant-sequence defect on p.9.
These are the fixed matrices printed in the source, not arbitrary existential witnesses. -/
theorem higherNormCounterexample :
    IsDensityMatrix counterX ∧ IsDensityMatrix counterY ∧
    (∀ t : ℝ, 0 < t →
      (Matrix.det ((t : ℂ) • (1 : Mat (Fin 3)) + counterX)).re -
        (Matrix.det ((t : ℂ) • (1 : Mat (Fin 3)) + counterY)).re = t/5000 + 161/500000) ∧
    (∀ t : ℝ, 0 < t → 0 < t/5000 + (161/500000 : ℝ)) ∧
    (∀ t : ℝ, 0 < t → logDet t counterY < logDet t counterX) ∧
    (counterX^3).trace.re = (61433/500000 : ℝ) ∧
    (counterY^3).trace.re = (49/400 : ℝ) ∧
    (49/400 : ℝ) < 61433/500000 ∧
    schatten 3 counterY < schatten 3 counterX ∧
    defect counterX counterY = (1/50 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
