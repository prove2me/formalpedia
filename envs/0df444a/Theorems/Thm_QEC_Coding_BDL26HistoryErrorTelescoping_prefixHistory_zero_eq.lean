-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_prefixHistory_zero_eq
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_zero_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:13:41.367492+00:00
-- url     : https://prove2.me/theorems/4e4d8883-1855-4028-8671-729dc580c7ee
-- title:
--   BDL26 History Error Telescoping: prefix History zero eq
-- statement:
--   Closed equations reduce the actual recursion's dependent Nat cases once.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L288-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L288-L302

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_zero_eq (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D) (s : D.family.Syndrome 0) :
    prefixHistory D st B 0 (Nat.zero_le _) s =
      [.base {
        input := s
        correction := B.decode s
        relation := (B.rightInverse s).symm }] := by sorry
