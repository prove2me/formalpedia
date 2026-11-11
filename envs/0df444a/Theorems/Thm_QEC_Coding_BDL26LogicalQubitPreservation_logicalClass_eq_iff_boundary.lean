-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalClass_eq_iff_boundary
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logicalClass_eq_iff_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:40:19.873502+00:00
-- url     : https://prove2.me/theorems/d19f6fda-4178-4930-83ce-7a12ddbd38ed
-- title:
--   BDL26 Logical Qubit Preservation: logical Class eq iff boundary
-- statement:
--   Equality is exactly a full-word actual coboundary, on arbitrary representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L80-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L80-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logicalClass_eq_iff_boundary (S : OddScale) (n : Nat)
    (u v : DualRepresentative S n) :
    logicalClass S n u = logicalClass S n v ↔
      ∃ f : Word Field (state S n).presentation.X,
        tannerCoboundary0 (state S n).presentation f = fun q => u.1 q - v.1 q := by sorry
