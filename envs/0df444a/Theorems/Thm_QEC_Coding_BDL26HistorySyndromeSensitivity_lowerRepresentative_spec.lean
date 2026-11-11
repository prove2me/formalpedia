-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_lowerRepresentative_spec
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.lowerRepresentative_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:55:50.4111+00:00
-- url     : https://prove2.me/theorems/d4af62ba-fdfe-428a-8e6a-9a5a0c3fd8b6
-- title:
--   BDL26 History Syndrome Sensitivity: lower Representative spec
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the lower Representative spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L52-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L52-L61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.lowerRepresentative_spec (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) :
    ((indexedDecoderData S d).selectedMap i).map1 (lowerRepresentative S d i hi e) =
      e + (actualStep S d i (errorInput S d i e)).correction +
        (indexedFamily S d).coboundary0 i.succ (fullPotential S d i hi e) ∧
    (indexedFamily S d).coboundary1 i.castSucc (lowerRepresentative S d i hi e) =
      (actualStep S d i (errorInput S d i e)).coarse.val ∧
    (indexedFamily S d).coboundary1 i.succ
      ((indexedFamily S d).coboundary0 i.succ (fullPotential S d i hi e)) = 0 := by sorry
