-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_atY
-- name    : ReciprocityTheory.ChartRestriction.L1.evalYZero_atY
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:25.555567+00:00
-- url     : https://prove2.me/theorems/7d060b37-7c10-455c-bec7-df628f197ed7
-- title:
--   L1: eval YZero at Y
-- statement:
--   The L1 construction uses the eval YZero at Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L93-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_Formalism_G_LogP_evalYZero_atY

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
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.L1.evalYZero_atY (φ : PowerSeries R) : ev0 (atY φ) = C (constantCoeff φ) := by sorry
