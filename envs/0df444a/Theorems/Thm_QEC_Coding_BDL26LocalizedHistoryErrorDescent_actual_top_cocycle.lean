-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_top_cocycle
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_top_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:24:18.311337+00:00
-- url     : https://prove2.me/theorems/2d4ae949-9752-495c-836e-793a700a60a1
-- title:
--   BDL26 Localized History Error Descent: actual top cocycle
-- statement:
--   The BDL26 Localized History Error Descent construction uses the actual top cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L832-L849
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L832-L849

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_top_cocycle :
    (Data S n).family.coboundary1 (TopIndex n)
      (e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
        historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e)))=0 := by sorry
