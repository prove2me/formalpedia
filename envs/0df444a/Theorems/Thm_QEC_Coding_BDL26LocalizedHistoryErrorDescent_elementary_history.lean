-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_elementary_history
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.elementary_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:18:27.818564+00:00
-- url     : https://prove2.me/theorems/252c850b-2ac9-4437-bff9-818ee0077a8c
-- title:
--   BDL26 Localized History Error Descent: elementary history
-- statement:
--   No caller incidence or lower-locality certificate enters an elementary flip.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L877-L889
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L877-L889

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.elementary_history (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (q : (state S (n+2)).presentation.Q) :
    let e := canonicalBasisWord (F := BDL26Field) q
    let x := elementaryCenter S n q
    let he := elementary_support S n q
    e+historyLiftedCorrection (Data S n) (actualHistory S n sigma)+
      historyLiftedCorrection (Data S n) (actualHistory S n (perturbTop S n sigma e))=
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((actualDescent S n sigma e x he 0).word+
          (actualBase S n).decode (actualInputs S n sigma 0)+
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0))+
      (Data S n).family.coboundary0 (TopIndex n) (actualPotential S n sigma e x he 0 (TopIndex n)) := by sorry
