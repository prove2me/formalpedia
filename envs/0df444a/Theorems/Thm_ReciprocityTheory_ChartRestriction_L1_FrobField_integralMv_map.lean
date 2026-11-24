-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_integralMv_map
-- name    : ReciprocityTheory.ChartRestriction.L1.FrobField.integralMv_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:16.464435+00:00
-- url     : https://prove2.me/theorems/4b27983d-4f13-49d7-afb4-c72ac80f952e
-- title:
--   Frob Field: integral Mv map
-- statement:
--   The Frob Field construction uses the integral Mv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L411-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L411-L415

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {l : ℕ} {σ : K →+* K} {ι : Type}

theorem ReciprocityTheory.ChartRestriction.L1.FrobField.integralMv_map (h : FrobField K l σ) {F : MvPowerSeries ι K} (hF : IntegralMv F) :
    IntegralMv (MvPowerSeries.map σ F) := by sorry
