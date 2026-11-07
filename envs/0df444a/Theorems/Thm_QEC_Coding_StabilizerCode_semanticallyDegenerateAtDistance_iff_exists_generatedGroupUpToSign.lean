-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign
-- name    : QEC.Coding.StabilizerCode.semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:11:44.111445+00:00
-- url     : https://prove2.me/theorems/1409c447-9c1c-412c-b543-1972ed8e7aed
-- title:
--   Stabilizer Code: semantically Degenerate At Distance iff exists generated Group Up To Sign
-- statement:
--   Semantic degeneracy below a finite distance is equivalent to a low-weight
--   nonidentity generated stabilizer representative. This realizes
--   [Gott97, Ch. 3, stabilizer distance and degeneracy paragraph].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean#L78-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean#L78-L96

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign
    (Q : SourceValidBinary ι) (d : Nat) :
    SemanticallyDegenerateAtDistance Q d ↔
      SemanticStabilizerDistance Q d ∧
      ∃ E : Binary ι,
        Q.1.InGeneratedGroupUpToSign E ∧
        ¬ BinaryUpToSign E (binaryOne (ι := ι)) ∧
        weight E < d := by sorry
