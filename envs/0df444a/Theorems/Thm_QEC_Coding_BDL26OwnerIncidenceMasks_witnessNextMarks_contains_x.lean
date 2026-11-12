-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessNextMarks_contains_x
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextMarks_contains_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:37:04.528702+00:00
-- url     : https://prove2.me/theorems/c6155d02-9be0-4df6-bc1c-ce96aa0d4e61
-- title:
--   BDL26 Owner Incidence Masks: witness Next Marks contains x
-- statement:
--   The real next-level syndrome marks its actual X owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L185-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean#L185-L197

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.witnessNextMarks_contains_x : Vertex.x evidenceX ∈ witnessNextMarks := by sorry
