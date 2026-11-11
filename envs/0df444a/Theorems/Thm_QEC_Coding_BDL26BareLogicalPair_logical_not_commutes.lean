-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logical_not_commutes
-- name    : QEC.Coding.BDL26BareLogicalPair.logical_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:24:17.23076+00:00
-- url     : https://prove2.me/theorems/96393ce3-4e0f-49fa-9bf0-d45e3d7e6db1
-- title:
--   BDL26 Bare Logical Pair: logical not commutes
-- statement:
--   The BDL26 Bare Logical Pair construction uses the logical not commutes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L154-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L154-L157

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

theorem QEC.Coding.BDL26BareLogicalPair.logical_not_commutes : ¬ Commutes (logicalX S m) (logicalZ S m) := by sorry
