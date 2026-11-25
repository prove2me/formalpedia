-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_kDens_mul
-- name    : ReciprocityTheory.AnForm.A.kDens_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:07:09.136438+00:00
-- url     : https://prove2.me/theorems/9d582a85-11ee-4ba5-a2b7-81b5cb202b6b
-- title:
--   A: k Dens mul
-- statement:
--   The A construction uses the k Dens mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L182-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L182-L189

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

theorem ReciprocityTheory.AnForm.A.kDens_mul : kDens n * (Real.pi / 2 * (1 / ((n : ℝ) + 1))) =
    (n.factorial : ℝ) * (2 / Real.pi) ^ n := by sorry
