-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_prefix_mk
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_prefix_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:40:10.92572+00:00
-- url     : https://prove2.me/theorems/5df368c2-76ef-4fb4-afde-69796db48620
-- title:
--   BDL26 Logical Qubit Preservation: logical Equiv prefix mk
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical Equiv prefix mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L117-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L117-L127

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_prefix_mk (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    logicalEquiv S n (logicalClass S n (prefixRepresentative S n w)) =
      BDL26SeedCohomology.coefficient w.1 := by sorry
