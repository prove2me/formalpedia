-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interval_equation
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.interval_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:02:29.824201+00:00
-- url     : https://prove2.me/theorems/344f40b8-f893-43c8-bd28-df4acb6b454e
-- title:
--   BDL26 Localized History Error Descent: interval equation
-- statement:
--   The BDL26 Localized History Error Descent construction uses the interval equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L542-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L542-L547

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.interval_equation (a b : LevelIndex n) (hab : a.val≤b.val) :
    intervalMap1 (Data S n) a b hab (path S n sigma tau top a).word=
      (path S n sigma tau top b).word+correctionIntervalSum S n sigma a b+
        correctionIntervalSum S n tau a b+(Data S n).family.coboundary0 b
          (intervalPotential S n sigma tau top a b) := by sorry
