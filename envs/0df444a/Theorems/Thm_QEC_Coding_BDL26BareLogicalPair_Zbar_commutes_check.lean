-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_commutes_check
-- name    : QEC.Coding.BDL26BareLogicalPair.Zbar_commutes_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:51:15.250218+00:00
-- url     : https://prove2.me/theorems/aced3881-fd4a-4357-84fb-4e151a356556
-- title:
--   BDL26 Bare Logical Pair: Zbar commutes check
-- statement:
--   The BDL26 Bare Logical Pair construction uses the Zbar commutes check property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L213-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L213-L215

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

theorem QEC.Coding.BDL26BareLogicalPair.Zbar_commutes_check (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (Zbar S m) (toQubitOperator (check S m j)) := by sorry
