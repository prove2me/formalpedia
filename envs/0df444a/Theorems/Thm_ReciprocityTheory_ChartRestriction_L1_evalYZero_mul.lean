-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_mul
-- name    : ReciprocityTheory.ChartRestriction.L1.evalYZero_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:31.848571+00:00
-- url     : https://prove2.me/theorems/155e8712-f985-5e94-90c7-38508ee6a9b2
-- title:
--   L1: eval YZero mul
-- statement:
--   The L1 construction uses the eval YZero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L47-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
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

theorem ReciprocityTheory.ChartRestriction.L1.evalYZero_mul (F G : MvPowerSeries (Fin 2) R) : ev0 (F * G) = ev0 F * ev0 G := by sorry
