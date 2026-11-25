-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_smul_single_one
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.smul_single_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:28.499792+00:00
-- url     : https://prove2.me/theorems/188bb46f-1ab7-5a27-a52c-834b93c1a0d7
-- title:
--   Trace Conjugation Cover: smul single one
-- statement:
--   The Trace Conjugation Cover construction uses the smul single one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L239-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L239-L244

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.smul_single_one (i : Fin D) (c : ℂ) :
    c • (Pi.single i 1 : Fin D → ℂ) = Pi.single i c := by sorry
