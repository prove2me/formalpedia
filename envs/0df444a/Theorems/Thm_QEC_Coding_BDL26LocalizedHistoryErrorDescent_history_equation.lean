-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_history_equation
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.history_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:07:16.419738+00:00
-- url     : https://prove2.me/theorems/a13f486f-b245-43c9-a030-488920010feb
-- title:
--   BDL26 Localized History Error Descent: history equation
-- statement:
--   Full original assembled prefixes, including their physical-C2 base words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L593-L620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L593-L620

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.history_equation :
    top.word+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
        historyLiftedCorrection (Data S n) (actualHistory S n tau)=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((path S n sigma tau top 0).word+(actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n tau 0))+
      (Data S n).family.coboundary0 (TopIndex n)
        (intervalPotential S n sigma tau top 0 (TopIndex n)) := by sorry
