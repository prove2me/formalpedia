-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_indexed_generator_word
-- name    : QEC.Coding.BDL26BareLogicalPair.indexed_generator_word
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:41:44.731661+00:00
-- url     : https://prove2.me/theorems/117c6f34-1d39-4c7d-a8b8-5b05ebd0845a
-- title:
--   BDL26 Bare Logical Pair: indexed generator word
-- statement:
--   The BDL26 Bare Logical Pair construction uses the indexed generator word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L330-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L330-L331

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

theorem QEC.Coding.BDL26BareLogicalPair.indexed_generator_word (depth : Nat) (i : MultiscaleDecoder.LevelIndex depth) :
    (indexedLogicalX S depth i).vector.xPart = (BDL26FiniteCohomology.generator S i.val (1 : ZMod 2)).val := by sorry
