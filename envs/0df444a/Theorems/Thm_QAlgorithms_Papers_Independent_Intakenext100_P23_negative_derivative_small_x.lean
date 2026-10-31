-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_negative_derivative_small_x
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.negative_derivative_small_x
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:34:50.069825+00:00
-- url     : https://prove2.me/theorems/5c176eb7-3918-4caf-b2aa-185cc77ad8fe
-- title:
--   Finite asymptotic expansion of the explicit negative-derivative integral
-- statement:
--   For $0<x<1$, use the defining convergent Gauss series for $F_z(x)={}_2F_1(z,1-z;1;x)$ and the principal logarithm continued from $F_z(0)=1$. Define the integrable real function
--   $$d(x)=-\int_{-\infty}^{\infty}\operatorname{Re}\left[\frac{\pi it}{\sin^2(\pi it)}\log F_{it}(x)\right]\,dt.$$
--   The value assigned at the single removable point $t=0$ does not affect the integral. As $x\to0^+$,
--   $$-d(x)=\frac{x}{3}+\frac{2x^2}{15}+\frac{26x^3}{315}+\frac{2x^4}{35}+\frac{52x^5}{1155}+\frac{302x^6}{9009}+\frac{76x^7}{2145}+\frac{398x^8}{255255}+\frac{327128x^9}{2297295}-\frac{18047684x^{10}}{24249225}+\frac{31378136x^{11}}{5311735}+O(x^{12}).$$
--   The remainder means that some $C>0$ and $\delta\in(0,1)$ bound its absolute value by $Cx^{12}$ for every $0<x<\delta$. This is a finite asymptotic target, not an infinite convergent series.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 30, Appendix D.2, Eq. (D.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source p.30, Eq.(D.8): finite one-sided asymptotic expansion of the
explicit integral (79). It is not an infinite convergent Taylor-series claim.
The first coefficient gives d(x)=-x/3+..., as required by (78). -/
theorem negative_derivative_small_x :
    (∀ x : ℝ, 0 < x → x < 1 →
      (∀ t : ℝ, Summable (complexHypergeometricTerm ((t : ℂ) * Complex.I) x)) ∧
      Integrable (negativeDerivativeIntegrand x)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ x : ℝ, 0 < x → x < delta →
        |-negativeReplicaDerivative x - negativeDerivativePolynomial x| ≤ C * x ^ 12 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
