-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_intervalPotential_succ
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:07:03.541581+00:00
-- url     : https://prove2.me/theorems/f95577a1-a75a-40c9-817c-891aca11eb34
-- title:
--   BDL26 Localized History Error Descent: interval Potential succ
-- statement:
--   The BDL26 Localized History Error Descent construction uses the interval Potential succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L489-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L489-L494

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_succ (a : LevelIndex n) (i : StepIndex n) (hai : a.val≤ i.val) :
    intervalPotential S n sigma tau top a i.succ=
      edgePotential S n sigma tau top i+
        ((Data S n).selectedMap i).map0 (intervalPotential S n sigma tau top a i.castSucc) := by sorry
