-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Zbar_adjoint
-- name    : QEC.Coding.BDL26BareLogicalPair.Zbar_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:09:45.311138+00:00
-- url     : https://prove2.me/theorems/1dd22f1e-158e-457d-ac16-9efcca015b47
-- title:
--   BDL26 Bare Logical Pair: Zbar adjoint
-- statement:
--   The BDL26 Bare Logical Pair construction uses the Zbar adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L187-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L187-L188

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

theorem QEC.Coding.BDL26BareLogicalPair.Zbar_adjoint : LinearMap.adjoint (Zbar S m) = Zbar S m := by sorry
