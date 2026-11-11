-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_even_pair
-- name    : QEC.Coding.BDL26BareLogicalPair.even_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:40:35.847089+00:00
-- url     : https://prove2.me/theorems/de5bf57a-ba5b-4703-b068-9954777336df
-- title:
--   BDL26 Bare Logical Pair: even pair
-- statement:
--   All source-even prefixes, including k=0, use this same selected pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L314-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L314-L321

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

theorem QEC.Coding.BDL26BareLogicalPair.even_pair (k : Nat) :
    (stabilizer S (2*k)).InBinaryNormalizer (logicalX S (2*k)) ∧
    (stabilizer S (2*k)).InBinaryNormalizer (logicalZ S (2*k)) ∧
    ¬ (stabilizer S (2*k)).InGeneratedGroupUpToSign (logicalX S (2*k)) ∧
    ¬ (stabilizer S (2*k)).InGeneratedGroupUpToSign (logicalZ S (2*k)) ∧
    Xbar S (2*k) * Zbar S (2*k) = -(Zbar S (2*k) * Xbar S (2*k)) := by sorry
