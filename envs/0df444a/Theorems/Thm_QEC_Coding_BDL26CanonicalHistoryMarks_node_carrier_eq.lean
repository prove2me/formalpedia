-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_node_carrier_eq
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.node_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:09:13.242371+00:00
-- url     : https://prove2.me/theorems/4fff1f71-53f9-4d5f-8273-817a2ab4f7bc
-- title:
--   BDL26 Canonical History Marks: node carrier eq
-- statement:
--   The BDL26 Canonical History Marks construction uses the node carrier eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L21-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L21-L21

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.node_carrier_eq : Node S n = (decodingGraph S (n + 2)).Node := by sorry
