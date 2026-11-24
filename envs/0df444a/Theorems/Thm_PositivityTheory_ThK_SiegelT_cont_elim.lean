-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_elim
-- name    : PositivityTheory.ThK.SiegelT.cont_elim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:16.908422+00:00
-- url     : https://prove2.me/theorems/be1232b9-7e20-48db-8ab6-7ec805cd73fc
-- title:
--   Siegel T: cont elim
-- statement:
--   The Siegel T construction uses the cont elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAn.lean#L36-L40

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

theorem PositivityTheory.ThK.SiegelT.cont_elim : Continuous fun z : (κ → R) × (κ' → R) => (Sum.elim z.1 z.2 : κ ⊕ κ' → R) := by sorry
