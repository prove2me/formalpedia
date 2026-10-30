-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_restricted_origin_excluded
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.restricted_origin_excluded
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:26:05.037129+00:00
-- url     : https://prove2.me/theorems/849da945-3a00-49f4-9cff-d840c178dfbe
-- title:
--   Restricted exclusion of the origin
-- statement:
--   For every integer qudit dimension $d\ge3$, no complex-linear CPTP $1\to2$ channel whose Choi matrix uses only the four rank-$d$ partially transposed permutations has both marginal shrink parameters zero:
--
--   $$
--   (0,0)\notin\mathcal R_d^{\mathrm{restricted}}.
--   $$
--
--   The parameters refer to the maps $D_p(X)=pX+(1-p)\operatorname{Tr}(X)I/d$. The dimension restriction is essential: at $d=2$ the origin is a boundary point of the restricted region.
--
--   This separates the restricted family from unrestricted cloning compatibility.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 10, Unnumbered exclusion of origin in the restricted family

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

/-- PDF p.10: exclusion of the origin is specific to the restricted family and d>=3. -/
theorem restricted_origin_excluded (d : ℕ) (hd : 3 ≤ d) :
    ¬ RestrictedAchievable d 0 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
