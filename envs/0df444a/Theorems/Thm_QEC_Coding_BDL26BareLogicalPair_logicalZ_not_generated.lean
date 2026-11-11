-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_not_generated
-- name    : QEC.Coding.BDL26BareLogicalPair.logicalZ_not_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:24:23.264869+00:00
-- url     : https://prove2.me/theorems/6e621ede-bf3d-411d-8c21-8eacfa75e1e3
-- title:
--   BDL26 Bare Logical Pair: logical Z not generated
-- statement:
--   The BDL26 Bare Logical Pair construction uses the logical Z not generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L159-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L159-L164

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

theorem QEC.Coding.BDL26BareLogicalPair.logicalZ_not_generated : ¬ (stabilizer S m).InGeneratedGroupUpToSign (logicalZ S m) := by sorry
