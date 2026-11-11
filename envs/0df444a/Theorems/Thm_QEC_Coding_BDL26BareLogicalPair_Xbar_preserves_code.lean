-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_preserves_code
-- name    : QEC.Coding.BDL26BareLogicalPair.Xbar_preserves_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:24:53.075439+00:00
-- url     : https://prove2.me/theorems/79e0955f-8220-4d83-bd5f-a994509302fb
-- title:
--   BDL26 Bare Logical Pair: Xbar preserves code
-- statement:
--   The BDL26 Bare Logical Pair construction uses the Xbar preserves code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L245-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L245-L250

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

theorem QEC.Coding.BDL26BareLogicalPair.Xbar_preserves_code (ψ : Qubit.QubitRegister (Physical S m))
    (hψ : ψ ∈ (labelledCode S m).carrier) : Xbar S m ψ ∈ (labelledCode S m).carrier := by sorry
