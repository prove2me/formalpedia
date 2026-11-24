-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_measurable_piecewise
-- name    : ReciprocityTheory.AnForm.A.PshMean.measurable_piecewise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:49.270648+00:00
-- url     : https://prove2.me/theorems/673e4c1c-efb2-4eb7-9ad4-6cb6c9c445f9
-- title:
--   Psh Mean: measurable piecewise
-- statement:
--   The Psh Mean construction uses the measurable piecewise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMean.lean#L35-L40

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

theorem ReciprocityTheory.AnForm.A.PshMean.measurable_piecewise {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by sorry
