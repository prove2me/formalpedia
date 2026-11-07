-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_not_semanticallyDegenerateAtDistance_iff_generated_weight_ge
-- name    : QEC.Coding.StabilizerCode.not_semanticallyDegenerateAtDistance_iff_generated_weight_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:11:55.861071+00:00
-- url     : https://prove2.me/theorems/5c350209-2722-4b67-a080-07ae8d24a47c
-- title:
--   Stabilizer Code: not semantically Degenerate At Distance iff generated weight ge
-- statement:
--   Under a finite semantic distance witness, nondegeneracy is exactly the lower
--   weight bound on every nonidentity generated stabilizer representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean#L102-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean#L102-L121

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

theorem QEC.Coding.StabilizerCode.not_semanticallyDegenerateAtDistance_iff_generated_weight_ge
    (Q : SourceValidBinary ι) (d : Nat)
    (hd : SemanticStabilizerDistance Q d) :
    ¬ SemanticallyDegenerateAtDistance Q d ↔
      ∀ E, Q.1.InGeneratedGroupUpToSign E →
        ¬ BinaryUpToSign E (binaryOne (ι := ι)) →
        d ≤ weight E := by sorry
