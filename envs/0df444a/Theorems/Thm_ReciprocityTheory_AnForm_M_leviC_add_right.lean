-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_leviC_add_right
-- name    : ReciprocityTheory.AnForm.M.leviC_add_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:10.959508+00:00
-- url     : https://prove2.me/theorems/0165eb24-2210-5e86-8559-7aabc58f5bda
-- title:
--   M: levi C add right
-- statement:
--   The M construction uses the levi C add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCIsHermitian.lean#L80-L84

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.M.leviC_add_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a b b' : Fin D → ℂ) :
    leviC H a (b + b') = leviC H a b + leviC H a b' := by sorry
