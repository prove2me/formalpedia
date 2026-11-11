-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_negative_order_action
-- name    : QEC.Coding.BDL26BareLogicalPair.negative_order_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:54:05.467311+00:00
-- url     : https://prove2.me/theorems/c65ded85-6536-45f8-90c1-652eba7b66c7
-- title:
--   BDL26 Bare Logical Pair: negative order action
-- statement:
--   The operator identity holds pointwise, including every actual code vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L281-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L281-L284

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

theorem QEC.Coding.BDL26BareLogicalPair.negative_order_action (ψ : Qubit.QubitRegister (Physical S m)) :
    (Xbar S m * Zbar S m) ψ = -((Zbar S m * Xbar S m) ψ) := by sorry
