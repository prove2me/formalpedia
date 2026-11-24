-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
-- name    : P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:42.459291+00:00
-- url     : https://prove2.me/theorems/14f09465-7248-40b1-8971-a3137aac9a2b
-- title:
--   P2 M Reciprocity Theory An Form A poly Max mono  555a93f5b347: P2 M Reciprocity Theory An Form A poly Max mono  555a93f5b347
-- statement:
--   The P2 M Reciprocity Theory An Form A poly Max mono  555a93f5b347 construction uses the P2 M Reciprocity Theory An Form A poly Max mono  555a93f5b347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L35-L38

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}

theorem P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347 (hφ : UpperSemicontinuousOn φ U) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : closedBall z t ⊆ U) : polyMax φ z s ≤ polyMax φ z t := by sorry

alias «ReciprocityTheory».«AnForm».«A».«polyMax_mono'» := P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
