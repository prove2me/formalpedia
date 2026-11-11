-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_Xbar_adjoint
-- name    : QEC.Coding.BDL26BareLogicalPair.Xbar_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:07:54.115193+00:00
-- url     : https://prove2.me/theorems/9728717c-384a-45b2-922c-fcdfa12c7509
-- title:
--   BDL26 Bare Logical Pair: Xbar adjoint
-- statement:
--   The BDL26 Bare Logical Pair construction uses the Xbar adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L185-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L185-L186

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

theorem QEC.Coding.BDL26BareLogicalPair.Xbar_adjoint : LinearMap.adjoint (Xbar S m) = Xbar S m := by sorry
