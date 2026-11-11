-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_commutes_check
-- name    : QEC.Coding.BDL26BareLogicalPair.Xbar_commutes_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:50:22.347591+00:00
-- url     : https://prove2.me/theorems/f8dc51b9-1325-4730-82bc-7305a178c535
-- title:
--   BDL26 Bare Logical Pair: Xbar commutes check
-- statement:
--   The BDL26 Bare Logical Pair construction uses the Xbar commutes check property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L209-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L209-L211

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

theorem QEC.Coding.BDL26BareLogicalPair.Xbar_commutes_check (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (Xbar S m) (toQubitOperator (check S m j)) := by sorry
