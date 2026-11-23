-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_sqForm_apply
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.sqForm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:21.985929+00:00
-- url     : https://prove2.me/theorems/e9f3141d-b0ba-4864-a37d-b56647168e53
-- title:
--   Trace Conjugation Cover: sq Form apply
-- statement:
--   The Trace Conjugation Cover construction uses the sq Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L210-L212

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.sqForm_apply (v u : Fin D → ℂ) :
    sqForm D v u = ∑ i, inner ℝ (v i) (u i) := by sorry
