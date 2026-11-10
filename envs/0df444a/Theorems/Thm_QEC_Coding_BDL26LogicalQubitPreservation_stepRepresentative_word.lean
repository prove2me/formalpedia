-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_stepRepresentative_word
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.stepRepresentative_word
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:41:39.770083+00:00
-- url     : https://prove2.me/theorems/809657a3-76c7-486c-9435-a0175c806adc
-- title:
--   BDL26 Logical Qubit Preservation: step Representative word
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the step Representative word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L157-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L157-L160

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.stepRepresentative_word (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    (stepRepresentative S n w).1 = BDL26AlternatingCochain.stepMap1 S n w.1 := by sorry
