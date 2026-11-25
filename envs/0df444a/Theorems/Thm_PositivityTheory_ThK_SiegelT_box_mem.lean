-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_box_mem
-- name    : PositivityTheory.ThK.SiegelT.box_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:22.926158+00:00
-- url     : https://prove2.me/theorems/296a45f6-d1c1-4806-ac87-78cee78d6e22
-- title:
--   Siegel T: box mem
-- statement:
--   The Siegel T construction uses the box mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L80-L86

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

theorem PositivityTheory.ThK.SiegelT.box_mem {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    (fun x : κ ⊕ κ' → R => φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → R) := by sorry
