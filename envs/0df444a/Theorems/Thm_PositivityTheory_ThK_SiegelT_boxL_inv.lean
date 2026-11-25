-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_boxL_inv
-- name    : PositivityTheory.ThK.SiegelT.boxL_inv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:18.365587+00:00
-- url     : https://prove2.me/theorems/f33fc1f1-c313-4ba2-a75f-1c6899275245
-- title:
--   Siegel T: box L inv
-- statement:
--   The Siegel T construction uses the box L inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L122-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L122-L142

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

theorem PositivityTheory.ThK.SiegelT.boxL_inv {A : Type} [CommRing A] [Invertible (2 : A)] [TopologicalSpace A] [T2Space A] [Fintype κ] {ψ : AddChar A ℂ}
    (hψ : ∀ x, ‖ψ x‖ = 1) {l : ((κ → A) → ℂ) →ₗ[ℂ] ℂ} {w₁ w₂ : (κ → A) × (κ → A)}
    (h₁ : ∀ φ ∈ SB (κ → A), l (schr ψ w₁ φ) = l φ) (h₂ : ∀ φ ∈ SB (κ → A), l (schr ψ w₂ φ) = l φ)
    {Φ : (κ ⊕ κ → A) → ℂ} (hΦ : Φ ∈ SB (κ ⊕ κ → A)) :
    boxL l (conjL l) (schr ψ (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 (-w₂.2)) Φ) = boxL l (conjL l) Φ := by sorry
