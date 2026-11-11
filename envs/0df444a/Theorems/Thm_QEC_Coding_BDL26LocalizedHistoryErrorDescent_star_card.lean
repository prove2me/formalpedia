-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_star_card
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.star_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:03:38.827206+00:00
-- url     : https://prove2.me/theorems/d0cdea22-0eef-4f06-9d9a-b36a2686f459
-- title:
--   BDL26 Localized History Error Descent: star card
-- statement:
--   This is a proved incidence bound on the actual state, not a caller radius.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L37-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L37-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.star_card (S : OddScale) (n : Nat) (a : LevelIndex n)
    (x : (state S (a.val+2)).presentation.X) : (star S n a x).card ≤ 7 := by sorry
