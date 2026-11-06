-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
-- name    : QEC.Coding.StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:41.87841+00:00
-- url     : https://prove2.me/theorems/7ac9a3a9-a317-496e-a0f1-0d5a4b0aac0c
-- title:
--   Stabilizer Code: semantic Stabilizer Distance iff min Weight in Binary Normalizer diff
-- statement:
--   For a source-valid binary stabilizer code, finite semantic Pauli distance is
--   exactly the attained least weight in the binary normalizer outside the
--   generated stabilizer up to sign. This realizes the distance characterization
--   of [Gott97, Ch. 2, distance paragraph; Ch. 3, stabilizer distance paragraph].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean#L52-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean#L52-L82

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
    (Q : SourceValidBinary ι) (d : Nat) :
    SemanticStabilizerDistance Q d ↔
      ∃ E : Binary ι,
        Q.1.InBinaryNormalizer E ∧
        ¬ Q.1.InGeneratedGroupUpToSign E ∧
        weight E = d ∧
        ∀ F : Binary ι,
          Q.1.InBinaryNormalizer F →
          ¬ Q.1.InGeneratedGroupUpToSign F →
          d ≤ weight F := by sorry
