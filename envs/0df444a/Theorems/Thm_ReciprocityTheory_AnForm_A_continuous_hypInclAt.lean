-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_hypInclAt
-- name    : ReciprocityTheory.AnForm.A.continuous_hypInclAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:52:07.512038+00:00
-- url     : https://prove2.me/theorems/8dcbb386-ea18-4893-8d20-85b2d79b8067
-- title:
--   A: continuous hyp Incl At
-- statement:
--   The A construction uses the continuous hyp Incl At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L167-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L167-L169

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.continuous_hypInclAt (i : Fin (n + 1)) : Continuous (hypInclAt (n := n) i) := by sorry
