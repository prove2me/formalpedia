-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_canonical_prefix_word
-- name    : QEC.Coding.BDL26BareLogicalPair.canonical_prefix_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:49:32.446477+00:00
-- url     : https://prove2.me/theorems/36f95086-c001-49e5-a1ce-8ab6b81a674a
-- title:
--   BDL26 Bare Logical Pair: canonical prefix word
-- statement:
--   The full selected word is the existing prefix map of the original seed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L69-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L69-L71

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

theorem QEC.Coding.BDL26BareLogicalPair.canonical_prefix_word : (canonicalGenerator S m).val =
    BDL26AlternatingCochain.map1 S m BDL26SeedCohomology.seedElement.val := by sorry
