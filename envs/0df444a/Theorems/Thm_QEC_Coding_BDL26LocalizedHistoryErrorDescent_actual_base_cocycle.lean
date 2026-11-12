-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_base_cocycle
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_base_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:25:16.322706+00:00
-- url     : https://prove2.me/theorems/834b80f9-f76f-494b-953e-dec7d209c779
-- title:
--   BDL26 Localized History Error Descent: actual base cocycle
-- statement:
--   The BDL26 Localized History Error Descent construction uses the actual base cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L825-L830
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L825-L830

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
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_base_cocycle :
    (Data S n).family.coboundary1 0
      ((actualDescent S n sigma e x he 0).word+
        (actualBase S n).decode (actualInputs S n sigma 0)+
        (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))=0 := by sorry
