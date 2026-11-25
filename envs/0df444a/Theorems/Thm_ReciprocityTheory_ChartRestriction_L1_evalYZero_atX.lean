-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_atX
-- name    : ReciprocityTheory.ChartRestriction.L1.evalYZero_atX
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:08.808702+00:00
-- url     : https://prove2.me/theorems/22f652f2-e657-4367-8c83-7fa8fdb7fe1b
-- title:
--   L1: eval YZero at X
-- statement:
--   The L1 construction uses the eval YZero at X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L86-L91

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

theorem ReciprocityTheory.ChartRestriction.L1.evalYZero_atX (φ : PowerSeries R) : ev0 (atX φ) = φ := by sorry
