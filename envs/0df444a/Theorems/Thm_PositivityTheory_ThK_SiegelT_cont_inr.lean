-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_inr
-- name    : PositivityTheory.ThK.SiegelT.cont_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:17.095804+00:00
-- url     : https://prove2.me/theorems/53b1e90f-c6c4-4956-9ad3-6170e84e0ed3
-- title:
--   Siegel T: cont inr
-- statement:
--   The Siegel T construction uses the cont inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L46-L46

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
omit [T2Space R]

theorem PositivityTheory.ThK.SiegelT.cont_inr : Continuous fun z : κ ⊕ κ' → R => z ∘ Sum.inr := by sorry
