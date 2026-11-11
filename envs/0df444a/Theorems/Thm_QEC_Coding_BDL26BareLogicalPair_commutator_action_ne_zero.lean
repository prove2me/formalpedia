-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_commutator_action_ne_zero
-- name    : QEC.Coding.BDL26BareLogicalPair.commutator_action_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:25:26.949803+00:00
-- url     : https://prove2.me/theorems/924a2fdb-3c77-4d9b-ba18-b99934a80260
-- title:
--   BDL26 Bare Logical Pair: commutator action ne zero
-- statement:
--   The BDL26 Bare Logical Pair construction uses the commutator action ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L294-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L294-L297

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

theorem QEC.Coding.BDL26BareLogicalPair.commutator_action_ne_zero (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) :
    (Xbar S m * Zbar S m - Zbar S m * Xbar S m) ψ ≠ 0 := by sorry
