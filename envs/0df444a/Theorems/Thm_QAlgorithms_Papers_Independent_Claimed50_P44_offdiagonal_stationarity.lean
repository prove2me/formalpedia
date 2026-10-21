-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_offdiagonal_stationarity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.offdiagonal_stationarity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:09:19.163609+00:00
-- url     : https://prove2.me/theorems/c31090e2-2957-45ad-8033-d21e375907ab
-- title:
--   Coordinate stationarity at diagonal gains
-- statement:
--   For a physical standard-form resource $A=aI$, $B=bI$, $C=\operatorname{diag}(c_1,c_2)$, let $D=\operatorname{diag}(d_1,d_2)$ be a physical pure-input covariance or the formal zero process matrix. Define the noise-optimized determinant $\mathcal D(S)=(|1-\det S|+\sqrt{\det M(S)})^2$, with $M$ as in Eq.(34). At every diagonal gain $S=\operatorname{diag}(x,y)$, both coordinate derivatives exist and satisfy
--
--   $$\left.\frac{\partial\mathcal D}{\partial s_{12}}\right|_{s_{12}=s_{21}=0}=0,\qquad \left.\frac{\partial\mathcal D}{\partial s_{21}}\right|_{s_{12}=s_{21}=0}=0.$$
--
--   This includes $xy=1$: varying either off-diagonal coordinate alone leaves the determinant unchanged. The assertion is coordinate stationarity, with no claim of joint differentiability or global diagonal optimality.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 5, §III, Eq.(42)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.5, Eq.(42): two coordinate derivatives of (40) vanish at diagonal
S, including det S=1. No joint differentiability or diagonal optimality claimed. -/
theorem offdiagonal_stationarity (a b c1 c2 d1 d2 x y : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2))
    (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    HasDerivAt (fun t : ℝ => reducedDet !![d1, 0; 0, d2]
      (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2] !![x, t; 0, y]) 0 0 ∧
    HasDerivAt (fun t : ℝ => reducedDet !![d1, 0; 0, d2]
      (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2] !![x, 0; t, y]) 0 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
