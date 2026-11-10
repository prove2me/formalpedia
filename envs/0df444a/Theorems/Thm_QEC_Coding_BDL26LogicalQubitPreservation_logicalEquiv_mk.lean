-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:32:59.180191+00:00
-- url     : https://prove2.me/theorems/76f07977-e020-42fb-a2e2-0afe7c4ab29f
-- title:
--   BDL26 Logical Qubit Preservation: logical Equiv mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L63-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L63-L69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_mk (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalEquiv S n (logicalClass S n w) =
      BDL26FiniteCohomology.finiteH1Equiv S n
        (BDL26FiniteCohomology.classOf S n (cocycleEquiv S n w)) := by sorry
