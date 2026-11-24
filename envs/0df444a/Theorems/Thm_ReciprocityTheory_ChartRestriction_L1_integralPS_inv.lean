-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_inv
-- name    : ReciprocityTheory.ChartRestriction.L1.integralPS_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:45.773821+00:00
-- url     : https://prove2.me/theorems/5845f2ca-27be-4ef1-a87f-b26ede8639e9
-- title:
--   L1: integral PS inv
-- statement:
--   The L1 construction uses the integral PS inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L174-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean#L174-L192

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

theorem ReciprocityTheory.ChartRestriction.L1.integralPS_inv {f : PowerSeries K} (hf : IntegralPS f) (h0 : ‖constantCoeff f‖ = 1) :
    IntegralPS f⁻¹ := by sorry
