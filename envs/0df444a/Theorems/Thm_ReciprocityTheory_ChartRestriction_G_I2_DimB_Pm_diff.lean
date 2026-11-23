-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Pm_diff
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimB.Pm_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:19.638356+00:00
-- url     : https://prove2.me/theorems/e800828f-6b1f-4d1b-aa52-97e202e6198a
-- title:
--   Dim B: Pm diff
-- statement:
--   The Dim B construction uses the Pm diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean#L261-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean#L261-L263

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

theorem ReciprocityTheory.ChartRestriction.G.I2.DimB.Pm_diff (h : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ h) (m : Fin k → ℤ) :
    Differentiable ℂ (Pm h m) := by sorry
