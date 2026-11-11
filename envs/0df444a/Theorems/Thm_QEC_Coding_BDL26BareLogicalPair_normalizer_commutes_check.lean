-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_normalizer_commutes_check
-- name    : QEC.Coding.BDL26BareLogicalPair.normalizer_commutes_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:25:42.882292+00:00
-- url     : https://prove2.me/theorems/f8ba4831-cf72-4dd6-acbf-77930062f943
-- title:
--   BDL26 Bare Logical Pair: normalizer commutes check
-- statement:
--   Ordinary bare normalizer semantics imply commutation with every original row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L197-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BareLogicalPair.lean#L197-L207

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

theorem QEC.Coding.BDL26BareLogicalPair.normalizer_commutes_check (E : Binary (Physical S m))
    (hE : (stabilizer S m).InBinaryNormalizer E) (j : Sum (ZLabel S m) (XLabel S m)) :
    Commute (toHermitianQubitOperator E) (toQubitOperator (check S m j)) := by sorry
