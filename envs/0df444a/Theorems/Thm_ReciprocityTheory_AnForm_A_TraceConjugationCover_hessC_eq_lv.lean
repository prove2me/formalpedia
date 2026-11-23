-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hessC_eq_lv
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.hessC_eq_lv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:11.160689+00:00
-- url     : https://prove2.me/theorems/ea88f66b-4189-4d6b-b028-2b072878f801
-- title:
--   Trace Conjugation Cover: hess C eq lv
-- statement:
--   The Trace Conjugation Cover construction uses the hess C eq lv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L14-L15

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.hessC_eq_lv {D : ℕ} (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    hessC f z i j = lv (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := by sorry
