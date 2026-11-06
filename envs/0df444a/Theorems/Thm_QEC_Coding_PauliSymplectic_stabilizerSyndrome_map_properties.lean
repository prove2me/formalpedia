-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndrome_map_properties
-- name    : QEC.Coding.PauliSymplectic.stabilizerSyndrome_map_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:27:14.826578+00:00
-- url     : https://prove2.me/theorems/0d0a5294-51d6-4986-8c9b-9ee39216936d
-- title:
--   Pauli Symplectic: stabilizer Syndrome map properties
-- statement:
--   The finite stabilizer syndrome laws: zero syndrome characterizes the generated
--   stabilizer normalizer, equal syndromes characterize a zero product syndrome,
--   and the source product has the same syndrome as the relative product under the
--   binary global-phase convention.  This is the source-exact bundled realization
--   of [Gott97, Ch. 3, error syndrome and Pauli pair-product convention].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1638-L1670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1638-L1670

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.stabilizerSyndrome_map_properties
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E A B : Binary ι) :
    (stabilizerSyndrome generators E = 0 ↔
      InStabilizerNormalizer generators E) ∧
    (stabilizerSyndrome generators A = stabilizerSyndrome generators B ↔
      stabilizerSyndrome generators (binaryMul A B) = 0) ∧
    stabilizerSyndrome generators (binaryMul A B) =
      stabilizerSyndrome generators (binaryMul (binaryDagger A) B) := by sorry
