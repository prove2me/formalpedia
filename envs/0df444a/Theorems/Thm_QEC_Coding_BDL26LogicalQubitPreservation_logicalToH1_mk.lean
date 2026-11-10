-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalToH1_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logicalToH1_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:33:55.662618+00:00
-- url     : https://prove2.me/theorems/955310f1-032b-48d0-a02a-45fcff1be5e6
-- title:
--   BDL26 Logical Qubit Preservation: logical To H1 mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical To H1 mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L53-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L53-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logicalToH1_mk (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalToH1 S n (logicalClass S n w) =
      BDL26FiniteCohomology.classOf S n (cocycleEquiv S n w) := by sorry
