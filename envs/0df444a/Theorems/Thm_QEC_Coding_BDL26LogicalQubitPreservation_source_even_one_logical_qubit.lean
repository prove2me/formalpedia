-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_source_even_one_logical_qubit
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.source_even_one_logical_qubit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:59:10.203867+00:00
-- url     : https://prove2.me/theorems/4a78fa05-c913-49c0-a884-256a479be317
-- title:
--   BDL26 Logical Qubit Preservation: source even one logical qubit
-- statement:
--   Source-even one-qubit assembly: semantic H1 and actual complex CSS code.
--   This internal theorem does not alter the public node's release state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L239-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L239-L249

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.source_even_one_logical_qubit (S : OddScale) (k : Nat) :
    Nonempty ((complex S (2*k)).middleCohomology ≃ₗ[Field] Field) ∧
      Module.finrank ℂ (BDL26CSSHamiltonian.labelledCode S (2*k)).carrier = 2 ∧
      (BDL26CSSHamiltonian.labelledCode S (2*k)).dimension = 2 ∧
      Fintype.card (BDL26CSSHamiltonian.Physical S (2*k)) -
        CSSGibbs.checkRank (BDL26CSSHamiltonian.zSyndrome S (2*k)) -
        CSSGibbs.checkRank (BDL26CSSHamiltonian.xSyndrome S (2*k)) = 1 := by sorry
