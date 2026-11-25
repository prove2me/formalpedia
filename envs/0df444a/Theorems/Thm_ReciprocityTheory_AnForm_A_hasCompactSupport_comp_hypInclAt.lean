-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hasCompactSupport_comp_hypInclAt
-- name    : ReciprocityTheory.AnForm.A.hasCompactSupport_comp_hypInclAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:19.741096+00:00
-- url     : https://prove2.me/theorems/6b448427-5217-55cf-b30d-21625d6730c9
-- title:
--   A: has Compact Support comp hyp Incl At
-- statement:
--   The A construction uses the has Compact Support comp hyp Incl At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L171-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L171-L180

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

theorem ReciprocityTheory.AnForm.A.hasCompactSupport_comp_hypInclAt (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ}
    (hhc : HasCompactSupport h) : HasCompactSupport (fun w : Fin n → ℂ => h (hypInclAt i w)) := by sorry
