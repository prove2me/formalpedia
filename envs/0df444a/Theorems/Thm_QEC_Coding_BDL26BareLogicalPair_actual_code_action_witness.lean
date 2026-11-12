-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_actual_code_action_witness
-- name    : QEC.Coding.BDL26BareLogicalPair.actual_code_action_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:39:14.862813+00:00
-- url     : https://prove2.me/theorems/d9099415-3477-4e6a-8316-2e92542b2b37
-- title:
--   BDL26 Bare Logical Pair: actual code action witness
-- statement:
--   An unconditional actual code-action witness; no codespace witness is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L300-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L300-L311

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

theorem QEC.Coding.BDL26BareLogicalPair.actual_code_action_witness : ∃ ψ : Qubit.QubitRegister (Physical S m),
    ψ ∈ (labelledCode S m).carrier ∧ ψ ≠ 0 ∧
    Xbar S m ψ ∈ (labelledCode S m).carrier ∧ Zbar S m ψ ∈ (labelledCode S m).carrier ∧
    (Xbar S m * Zbar S m) ψ ∈ (labelledCode S m).carrier ∧
    Xbar S m ψ ≠ 0 ∧ Zbar S m ψ ≠ 0 ∧ (Xbar S m * Zbar S m) ψ ≠ 0 ∧
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ ≠ 0 := by sorry
