-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_integrable_fd
-- name    : ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.integrable_fd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:23.677628+00:00
-- url     : https://prove2.me/theorems/fd535859-ab95-48d8-abdd-6a9598a29a16
-- title:
--   Flat Weighted Estimates: integrable fd
-- statement:
--   The Flat Weighted Estimates construction uses the integrable fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L33-L38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates

theorem ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.integrable_fd {n : ℕ} {f : V n → ℂ} (hf : LocallyIntegrable f volume) {φ : V n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (u : V n) :
    Integrable (fun y => f y * fderiv ℝ φ y u) volume := by sorry
