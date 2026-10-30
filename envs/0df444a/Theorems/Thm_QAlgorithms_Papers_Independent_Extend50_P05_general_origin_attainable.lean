-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_general_origin_attainable
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.general_origin_attainable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:27:27.882254+00:00
-- url     : https://prove2.me/theorems/061692d7-681b-468a-9f0c-bbccf244ebe8
-- title:
--   Unrestricted attainability of the origin
-- statement:
--   For every integer qudit dimension $d\ge2$, a complex-linear CPTP map from one qudit to two ordered qudits exists with both marginal maps completely depolarizing:
--
--   $$
--   (p,q)=(0,0)\in\mathcal R_d,
--   \qquad T_1(X)=T_2(X)=\operatorname{Tr}(X)I/d.
--   $$
--
--   The origin is a pair of shrink parameters, rather than the zero-operator map. For example, the joint completely depolarizing map sends $X$ to $\operatorname{Tr}(X)I_{d^2}/d^2$.
--
--   This exhibits a feasible quality pair absent from the restricted family when $d\ge3$.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 13, Unnumbered general-family attainability of origin

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.13: unrestricted channels attain the origin in every nontrivial qudit dimension.
The origin denotes two completely depolarizing marginals, not a zero channel. -/
theorem general_origin_attainable (d : ℕ) (hd : 2 ≤ d) :
    CloningAchievable d 0 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
