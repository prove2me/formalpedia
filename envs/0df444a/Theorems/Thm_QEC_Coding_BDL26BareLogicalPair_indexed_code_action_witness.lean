-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_indexed_code_action_witness
-- name    : QEC.Coding.BDL26BareLogicalPair.indexed_code_action_witness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:39:50.361813+00:00
-- url     : https://prove2.me/theorems/d0c4d7b5-ecdc-49e2-b835-1752a13e8bb2
-- title:
--   BDL26 Bare Logical Pair: indexed code action witness
-- statement:
--   The BDL26 Bare Logical Pair construction uses the indexed code action witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L343-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L343-L352

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)

theorem QEC.Coding.BDL26BareLogicalPair.indexed_code_action_witness (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    ∃ ψ : Qubit.QubitRegister (BDL26IndexedDecoder.FamilyQ S depth i),
      ψ ∈ (indexedLabelledCode S depth i).carrier ∧ ψ ≠ 0 ∧
      (toHermitianQubitOperator (indexedLogicalX S depth i) *
        toHermitianQubitOperator (indexedLogicalZ S depth i)) ψ ≠ 0 ∧
      (toHermitianQubitOperator (indexedLogicalX S depth i) * toHermitianQubitOperator (indexedLogicalZ S depth i) -
        toHermitianQubitOperator (indexedLogicalZ S depth i) * toHermitianQubitOperator (indexedLogicalX S depth i)) ψ ≠ 0 := by sorry
