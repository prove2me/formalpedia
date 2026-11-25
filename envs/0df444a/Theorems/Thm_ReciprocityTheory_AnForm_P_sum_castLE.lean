-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_sum_castLE
-- name    : ReciprocityTheory.AnForm.P.sum_castLE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:28.275396+00:00
-- url     : https://prove2.me/theorems/db34df93-dbc0-497c-96e6-298a2d90c252
-- title:
--   P: sum cast LE
-- statement:
--   The P construction uses the sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L112-L118

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

theorem ReciprocityTheory.AnForm.P.sum_castLE (N m : ℕ) (hm : m ≤ N) (f : Fin N → ℝ) :
    ∑ b : Fin m, f (Fin.castLE hm b) = ∑ k : Fin N, if k.val < m then f k else 0 := by sorry
