-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_local_equation
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_local_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:10:52.764397+00:00
-- url     : https://prove2.me/theorems/8f996892-7221-4a86-9af8-a55fbe697382
-- title:
--   BDL26 Localized History Error Descent: path local equation
-- statement:
--   The BDL26 Localized History Error Descent construction uses the path local equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L393-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L393-L399

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_local_equation (i : StepIndex n) :
    ((Data S n).selectedMap i).map1 (path S n sigma tau top i.castSucc).word=
      (path S n sigma tau top i.succ).word+
        (actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (Data S n).family.coboundary0 i.succ (edgePotential S n sigma tau top i) := by sorry
