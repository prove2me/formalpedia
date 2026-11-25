-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_sqForm_single
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.sqForm_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:40.20747+00:00
-- url     : https://prove2.me/theorems/a9d584cc-42b5-4ca7-a054-84d71273e747
-- title:
--   Trace Conjugation Cover: sq Form single
-- statement:
--   The Trace Conjugation Cover construction uses the sq Form single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L230-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L230-L237

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.sqForm_single (i j : Fin D) (a b : ℂ) :
    sqForm D (Pi.single i a) (Pi.single j b) = if i = j then inner ℝ a b else 0 := by sorry
