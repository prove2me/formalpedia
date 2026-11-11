-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_product_action_ne_zero
-- name    : QEC.Coding.BDL26BareLogicalPair.product_action_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:53:16.134018+00:00
-- url     : https://prove2.me/theorems/4c65af62-ba3a-46bc-a7cc-bf394d0d6dce
-- title:
--   BDL26 Bare Logical Pair: product action ne zero
-- statement:
--   The BDL26 Bare Logical Pair construction uses the product action ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L277-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L277-L278

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

theorem QEC.Coding.BDL26BareLogicalPair.product_action_ne_zero (ψ : Qubit.QubitRegister (Physical S m)) (hψ : ψ ≠ 0) :
    (Xbar S m * Zbar S m) ψ ≠ 0 := by sorry
