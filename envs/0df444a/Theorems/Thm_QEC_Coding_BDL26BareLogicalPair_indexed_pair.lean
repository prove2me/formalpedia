-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_indexed_pair
-- name    : QEC.Coding.BDL26BareLogicalPair.indexed_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:39:38.733052+00:00
-- url     : https://prove2.me/theorems/b6dd7b5c-d8fa-4f91-aa0a-c92db21883b7
-- title:
--   BDL26 Bare Logical Pair: indexed pair
-- statement:
--   The BDL26 Bare Logical Pair construction uses the indexed pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L333-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L333-L341

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

theorem QEC.Coding.BDL26BareLogicalPair.indexed_pair (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    (stabilizer S i.val).InBinaryNormalizer (indexedLogicalX S depth i) ∧
    (stabilizer S i.val).InBinaryNormalizer (indexedLogicalZ S depth i) ∧
    ¬ (stabilizer S i.val).InGeneratedGroupUpToSign (indexedLogicalX S depth i) ∧
    ¬ (stabilizer S i.val).InGeneratedGroupUpToSign (indexedLogicalZ S depth i) ∧
    toHermitianQubitOperator (indexedLogicalX S depth i) * toHermitianQubitOperator (indexedLogicalZ S depth i) =
      -(toHermitianQubitOperator (indexedLogicalZ S depth i) * toHermitianQubitOperator (indexedLogicalX S depth i)) := by sorry
