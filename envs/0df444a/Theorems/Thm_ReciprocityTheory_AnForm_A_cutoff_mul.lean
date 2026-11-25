-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_cutoff_mul
-- name    : ReciprocityTheory.AnForm.A.cutoff_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:10.895268+00:00
-- url     : https://prove2.me/theorems/cec5be76-92af-5f6f-a01f-e0bc91ac84fa
-- title:
--   A: cutoff mul
-- statement:
--   The A construction uses the cutoff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L142-L152

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
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
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.cutoff_mul {χ φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hts : tsupport χ ⊆ U) (hφ : ContDiffOn ℝ 3 φ U) :
    ContDiff ℝ 3 (fun x => χ x * φ x) := by sorry
