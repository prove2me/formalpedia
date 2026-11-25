-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_boxL_box
-- name    : PositivityTheory.ThK.SiegelT.boxL_box
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:11.887495+00:00
-- url     : https://prove2.me/theorems/88c16d7b-fda7-45ed-9d0d-72ede556a04a
-- title:
--   Siegel T: box L box
-- statement:
--   The Siegel T construction uses the box L box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L111-L120

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
variable {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type}

theorem PositivityTheory.ThK.SiegelT.boxL_box {A : Type} (l : ((κ → A) → ℂ) →ₗ[ℂ] ℂ) (l' : ((κ' → A) → ℂ) →ₗ[ℂ] ℂ) (φ₁ : (κ → A) → ℂ) (φ₂ : (κ' → A) → ℂ) :
    boxL l l' (fun x => φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr)) = l φ₁ * l' φ₂ := by sorry
