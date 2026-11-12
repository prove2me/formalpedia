-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logical_class_normal_form
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logical_class_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:48:59.878556+00:00
-- url     : https://prove2.me/theorems/8db9ac0d-61bc-4054-9419-8da57eb291e2
-- title:
--   BDL26 Logical Qubit Preservation: logical class normal form
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical class normal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L140-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L140-L144

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logical_class_normal_form (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalClass S n w = logicalClass S n (prefixRepresentative S n
      (logicalEquiv S n (logicalClass S n w) • BDL26SeedCohomology.seedElement)) := by sorry
