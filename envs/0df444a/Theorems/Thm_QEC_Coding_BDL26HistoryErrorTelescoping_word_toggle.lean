-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_toggle
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.word_toggle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:00:16.609446+00:00
-- url     : https://prove2.me/theorems/ddda3810-8e7f-4dd9-9337-27361e37436e
-- title:
--   BDL26 History Error Telescoping: word toggle
-- statement:
--   F2 cancellation is coordinatewise, including empty coordinate carriers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L26-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L26-L30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w

theorem QEC.Coding.BDL26HistoryErrorTelescoping.word_toggle {I : Type u} (x y p : Word BDL26Field I) (h : x=y+p) : y=x+p := by sorry
