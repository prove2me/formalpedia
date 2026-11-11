-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_prefixHistory_through
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:12:13.015572+00:00
-- url     : https://prove2.me/theorems/f140ede1-706b-4d69-ab66-732eae231096
-- title:
--   BDL26 History Error Telescoping: prefix History through
-- statement:
--   Filtering the original recursion keeps precisely its same-provider prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L250-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L250-L285

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_through (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (m : Nat) (hm : m ≤ depth)
    (s : D.family.Syndrome ⟨m,Nat.lt_succ_of_le hm⟩)
    (b : LevelIndex depth) (hb : b.val ≤ m) :
    historyThrough D (prefixHistory D st B m hm s) b =
      prefixHistory D st B b.val (hb.trans hm) (prefixInput D st m hm s b hb) := by sorry
