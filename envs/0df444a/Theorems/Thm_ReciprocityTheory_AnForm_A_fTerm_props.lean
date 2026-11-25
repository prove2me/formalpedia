-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fTerm_props
-- name    : ReciprocityTheory.AnForm.A.fTerm_props
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:40.032023+00:00
-- url     : https://prove2.me/theorems/845e47fa-2846-4435-8fba-9a3b0a577b3a
-- title:
--   A: f Term props
-- statement:
--   The A construction uses the f Term props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L94-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L94-L128

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

theorem ReciprocityTheory.AnForm.A.fTerm_props (i : Fin (n + 1)) {h : (Fin (n + 1) → ℂ) → ℝ} (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (j k : Fin (n + 1)) :
    Integrable (fTerm i h j k) ∧ ∫ z, fTerm i h j k z =
      if j = i ∧ k = i then
        (Real.pi / 2) * (1 / ((n : ℝ) + 1)) * ∫ w, h (Fin.insertNth i 0 w)
      else 0 := by sorry
