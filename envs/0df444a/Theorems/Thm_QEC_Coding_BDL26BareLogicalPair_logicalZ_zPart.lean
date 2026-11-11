-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_zPart
-- name    : QEC.Coding.BDL26BareLogicalPair.logicalZ_zPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:05:59.349369+00:00
-- url     : https://prove2.me/theorems/0e445c57-af4b-4542-b6f8-193a854ed669
-- title:
--   BDL26 Bare Logical Pair: logical Z z Part
-- statement:
--   The BDL26 Bare Logical Pair construction uses the logical Z z Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L138-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L138-L138

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

theorem QEC.Coding.BDL26BareLogicalPair.logicalZ_zPart : (logicalZ S m).vector.zPart = partnerWord S m := by sorry

attribute [defeq] QEC.Coding.BDL26BareLogicalPair.logicalZ_zPart
