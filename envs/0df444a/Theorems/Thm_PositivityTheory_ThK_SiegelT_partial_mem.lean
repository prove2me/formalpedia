-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_partial_mem
-- name    : PositivityTheory.ThK.SiegelT.partial_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:24.099175+00:00
-- url     : https://prove2.me/theorems/b6439b00-91a9-464b-ac4a-86505ff3d045
-- title:
--   Siegel T: partial mem
-- statement:
--   The Siegel T construction uses the partial mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L55-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L55-L78

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

theorem PositivityTheory.ThK.SiegelT.partial_mem {Φ : (κ ⊕ κ' → R) → ℂ} (h : Φ ∈ SB (κ ⊕ κ' → R)) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) :
    (fun y : κ' → R => l fun x => Φ (Sum.elim x y)) ∈ SB (κ' → R) := by sorry
