-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_lower_weight
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_lower_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:11:17.502379+00:00
-- url     : https://prove2.me/theorems/c375f24f-5639-44a0-a8f7-2a80a9cfe8be
-- title:
--   BDL26 Localized History Error Descent: path lower weight
-- statement:
--   These are bounds on the constructed LOWER word, never on full corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L412-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L412-L417

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
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_lower_weight (a : LevelIndex n) (_below : a.val<n) :
    HammingWeight (path S n sigma tau top a).word ≤
        (star S n a (path S n sigma tau top a).center).card ∧
      (star S n a (path S n sigma tau top a).center).card ≤ 7 := by sorry
