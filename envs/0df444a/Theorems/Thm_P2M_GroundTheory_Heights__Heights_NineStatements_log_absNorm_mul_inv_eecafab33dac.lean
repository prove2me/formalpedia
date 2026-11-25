-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_mul_inv_eecafab33dac
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_mul_inv_eecafab33dac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:24.224834+00:00
-- url     : https://prove2.me/theorems/800db035-45d8-5b74-ae19-00590a6080ca
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements log abs Norm mul inv eecafab33dac: P2 M Ground Theory Heights  Heights Nine Statements log abs Norm mul inv eecafab33dac
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements log abs Norm mul inv eecafab33dac construction uses the P2 M Ground Theory Heights  Heights Nine Statements log abs Norm mul inv eecafab33dac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L59-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_mul_inv_eecafab33dac {L : Type} [Field L] [NumberField L] {a b : FractionalIdeal (𝓞 L)⁰ L}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (FractionalIdeal.absNorm (a * b⁻¹) : ℝ) =
      Real.log (FractionalIdeal.absNorm a : ℝ) - Real.log (FractionalIdeal.absNorm b : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«log_absNorm_mul_inv» := P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_mul_inv_eecafab33dac
