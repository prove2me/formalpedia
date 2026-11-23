-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_mF_tproj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimB.mF_tproj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:12.474016+00:00
-- url     : https://prove2.me/theorems/4b400567-3346-4b96-bf12-a80452a231cf
-- title:
--   Dim B: m F tproj
-- statement:
--   The Dim B construction uses the m F tproj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean#L95-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16

theorem ReciprocityTheory.ChartRestriction.G.I2.DimB.mF_tproj (m : Fin k → ℤ) (x : Fin k → ℝ) :
    UnitAddTorus.mFourier m (tproj x) = cexp (2 * Real.pi * I * ∑ l, (m l : ℂ) * (x l : ℂ)) := by sorry
