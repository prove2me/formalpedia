-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_sW_pairs
-- name    : ReciprocityTheory.AnForm.P.sW_pairs
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:35.647882+00:00
-- url     : https://prove2.me/theorems/89453f8d-9d14-4bd1-a866-c3be172b13e7
-- title:
--   P: s W pairs
-- statement:
--   The P construction uses the s W pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L168-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L168-L185

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial

theorem ReciprocityTheory.AnForm.P.sW_pairs (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m w = ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
      hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0 := by sorry
