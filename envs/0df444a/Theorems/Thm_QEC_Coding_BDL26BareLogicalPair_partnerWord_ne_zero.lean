-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_partnerWord_ne_zero
-- name    : QEC.Coding.BDL26BareLogicalPair.partnerWord_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:51:22.371213+00:00
-- url     : https://prove2.me/theorems/9ae4144d-b7eb-4a28-85ce-75bdbea0821f
-- title:
--   BDL26 Bare Logical Pair: partner Word ne zero
-- statement:
--   The BDL26 Bare Logical Pair construction uses the partner Word ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L124-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L124-L131

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

theorem QEC.Coding.BDL26BareLogicalPair.partnerWord_ne_zero : partnerWord S m ≠ 0 := by sorry
