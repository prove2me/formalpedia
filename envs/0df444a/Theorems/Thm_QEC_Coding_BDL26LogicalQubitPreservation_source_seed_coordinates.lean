-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_source_seed_coordinates
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.source_seed_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:58:09.020039+00:00
-- url     : https://prove2.me/theorems/ffeab85f-ea6e-48c7-96f3-13e6e0732c18
-- title:
--   BDL26 Logical Qubit Preservation: source seed coordinates
-- statement:
--   The literal source seed retains its two/five/two coordinate spaces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L225-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L225-L235

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.source_seed_coordinates (S : OddScale) :
    Fintype.card (state S 0).presentation.X = 2 ∧
      Fintype.card (state S 0).presentation.Q = 5 ∧
      Fintype.card (state S 0).presentation.Z = 2 := by sorry
