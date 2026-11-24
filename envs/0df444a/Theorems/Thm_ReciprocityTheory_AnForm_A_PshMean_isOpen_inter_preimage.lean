-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
-- name    : ReciprocityTheory.AnForm.A.PshMean.isOpen_inter_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:32.275855+00:00
-- url     : https://prove2.me/theorems/1529faf6-e8c5-44be-97dd-287d715ef55b
-- title:
--   Psh Mean: is Open inter preimage
-- statement:
--   The Psh Mean construction uses the is Open inter preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L26-L33

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.PshMean.isOpen_inter_preimage {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) (y : ℝ) : IsOpen (φ ⁻¹' Iio y ∩ U) := by sorry
