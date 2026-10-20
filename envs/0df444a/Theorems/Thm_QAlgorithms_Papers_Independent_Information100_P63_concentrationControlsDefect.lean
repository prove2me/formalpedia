-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P63_concentrationControlsDefect
-- name    : QAlgorithms.Papers.Independent.Information100.P63.concentrationControlsDefect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:37:10.127949+00:00
-- url     : https://prove2.me/theorems/8f3ec6c6-2fc1-4ba4-abc8-af10f3c7deee
-- title:
--   Spectral anti-concentration controls majorization defect
-- statement:
--   Throughout, a state is a positive semidefinite complex matrix of unnormalized trace one. All spaces have positive finite dimension. Write $\log=\log_2$, use $\ln$ for natural logarithms, and set $0\log 0=0$. For states $X,Y$ on a common $D$-dimensional space, let $K_k(X)$ be the sum of the $k$ largest eigenvalues, counted with multiplicity, and let $\delta_{\rm maj}(X,Y)=\max_{0\le k\le D}(K_k(X)-K_k(Y))$. For $t>0$, put $L_t(X)=\ln\det(tI+X)$.
--
--   If $y_1,\ldots,y_D$ are the eigenvalues of $Y$, let $S_Y=-\log y_J$, where $\Pr(J=j)=y_j$; zero eigenvalues are never sampled. Define $q(Y)=\sup_{a\in\mathbb R}\Pr(a<S_Y\le a+1)$, which lies in $(0,1]$.
--
--   Let $X,Y$ be states on the same space and assume $L_t(X)\ge L_t(Y)$ for every $t>0$. Then
--
--   $$
--   \delta_{\rm maj}(X,Y)\le q(Y)\left[3+2\ln\ln\frac{e}{q(Y)}\right].
--   $$
--
--   Here $e=\exp(1)$. The estimate converts a log-determinant ordering into an explicit spectral defect bound, with no channel or tensor assumption.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, PDF p. 7, Proposition 6, Eq. (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 6, Eq.(33), PDF pp.7–8. `q` is the actual spectral concentration. -/
theorem concentrationControlsDefect (D : ℕ) (hD : 0 < D) (X Y : Mat (Fin D))
    (hX : IsDensityMatrix X) (hY : IsDensityMatrix Y)
    (horder : ∀ t : ℝ, 0 < t → logDet t Y ≤ logDet t X) :
    defect X Y ≤ concentration Y *
      (3 + 2 * Real.log (Real.log (Real.exp 1 / concentration Y))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P63

end
