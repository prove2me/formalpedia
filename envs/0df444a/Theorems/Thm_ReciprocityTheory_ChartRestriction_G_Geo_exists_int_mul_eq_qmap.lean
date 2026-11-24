-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_int_mul_eq_qmap
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_int_mul_eq_qmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:05.74881+00:00
-- url     : https://prove2.me/theorems/2ffc85b7-85b5-4de7-a5c2-2af845ebbe56
-- title:
--   Geo: exists int mul eq qmap
-- statement:
--   The Geo construction uses the exists int mul eq qmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L17-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_int_mul_eq_qmap (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by sorry
