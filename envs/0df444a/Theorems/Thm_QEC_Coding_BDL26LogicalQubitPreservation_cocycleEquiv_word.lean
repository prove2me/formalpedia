-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_word
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.cocycleEquiv_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:36:38.886433+00:00
-- url     : https://prove2.me/theorems/a42e85a7-e9c2-4846-852a-6e133d2717ea
-- title:
--   BDL26 Logical Qubit Preservation: cocycle Equiv word
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the cocycle Equiv word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L36-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L36-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.cocycleEquiv_word (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    (cocycleEquiv S n w).1 = w.1 := by sorry
