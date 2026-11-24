-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_star_mem
-- name    : PositivityTheory.ThK.SiegelT.star_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:00.531299+00:00
-- url     : https://prove2.me/theorems/bee2faf6-9bd3-4fcb-8c7b-24c1e2484778
-- title:
--   Siegel T: star mem
-- statement:
--   The Siegel T construction uses the star mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L88-L89

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

theorem PositivityTheory.ThK.SiegelT.star_mem {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) : star φ ∈ SB X := by sorry
