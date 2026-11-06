-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_exists_semanticStabilizerDistance_iff_exists_logicalPauli
-- name    : QEC.Coding.StabilizerCode.exists_semanticStabilizerDistance_iff_exists_logicalPauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:41:52.91723+00:00
-- url     : https://prove2.me/theorems/3a5dc9f3-ff46-4d62-8835-1cd7b4adccb0
-- title:
--   Stabilizer Code: exists semantic Stabilizer Distance iff exists logical Pauli
-- statement:
--   A finite semantic stabilizer distance exists exactly when the binary normalizer
--   logical sector is nonempty. The forward implication uses the attained semantic
--   witness; the reverse implication minimizes weight over the finite binary Pauli
--   space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean#L90-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean#L90-L117

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

theorem QEC.Coding.StabilizerCode.exists_semanticStabilizerDistance_iff_exists_logicalPauli
    (Q : SourceValidBinary ι) :
    (∃ d, SemanticStabilizerDistance Q d) ↔
      ∃ E, Q.1.InBinaryNormalizer E ∧
        ¬ Q.1.InGeneratedGroupUpToSign E := by sorry
