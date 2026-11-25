-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_of_zero_outside
-- name    : ReciprocityTheory.AnForm.A.contDiff_of_zero_outside
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:11.508675+00:00
-- url     : https://prove2.me/theorems/dad76fd6-6e74-43e1-86f7-12022d2f6c83
-- title:
--   A: cont Diff of zero outside
-- statement:
--   The A construction uses the cont Diff of zero outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L9-L20

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.A.contDiff_of_zero_outside {D : ℕ} {f : (Fin D → ℂ) → ℂ} {U K : Set (Fin D → ℂ)}
    {m : WithTop ℕ∞} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hf : ContDiffOn ℝ m f U)
    (h0 : ∀ y ∉ K, f y = 0) : ContDiff ℝ m f := by sorry
