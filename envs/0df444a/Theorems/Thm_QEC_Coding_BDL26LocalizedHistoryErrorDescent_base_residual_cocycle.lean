-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_base_residual_cocycle
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.base_residual_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:12:05.593212+00:00
-- url     : https://prove2.me/theorems/968c5745-8544-49c7-b2b3-1d3f098297dd
-- title:
--   BDL26 Localized History Error Descent: base residual cocycle
-- statement:
--   The BDL26 Localized History Error Descent construction uses the base residual cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L622-L634
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L622-L634

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.base_residual_cocycle :
    (Data S n).family.coboundary1 0
      ((path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n tau 0))=0 := by sorry
