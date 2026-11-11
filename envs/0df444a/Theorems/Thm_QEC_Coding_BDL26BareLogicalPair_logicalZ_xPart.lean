-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_xPart
-- name    : QEC.Coding.BDL26BareLogicalPair.logicalZ_xPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:06:50.901591+00:00
-- url     : https://prove2.me/theorems/a95418e3-c36b-4946-9c22-7d87944fa29d
-- title:
--   BDL26 Bare Logical Pair: logical Z x Part
-- statement:
--   The BDL26 Bare Logical Pair construction uses the logical Z x Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L137-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L137-L137

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

theorem QEC.Coding.BDL26BareLogicalPair.logicalZ_xPart : (logicalZ S m).vector.xPart = 0 := by sorry

attribute [defeq] QEC.Coding.BDL26BareLogicalPair.logicalZ_xPart
