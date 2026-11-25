-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_eval_cpP
-- name    : ReciprocityTheory.AnForm.P.eval_cpP
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:00.136362+00:00
-- url     : https://prove2.me/theorems/538a5c98-58ab-5997-a59a-970dfcdb2f6c
-- title:
--   P: eval cp P
-- statement:
--   The P construction uses the eval cp P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L269-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L269-L274

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.P.eval_cpP (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    (cpP N A).map (eval t) = ∑ k ∈ Finset.range N, (t ^ k * ((k.factorial : ℂ)⁻¹)) • A ^ k := by sorry
