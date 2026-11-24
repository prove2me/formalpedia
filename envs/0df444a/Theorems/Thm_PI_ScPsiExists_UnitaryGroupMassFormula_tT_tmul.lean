-- Prove2me | Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tT_tmul
-- name    : PI.ScPsiExists.UnitaryGroupMassFormula.tT_tmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:20.898545+00:00
-- url     : https://prove2.me/theorems/8e4b6d6c-8272-41a3-a1e4-4f06f8dead62
-- title:
--   Unitary Group Mass Formula: t T tmul
-- statement:
--   The Unitary Group Mass Formula construction uses the t T tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean#L109-L111

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.ScPsiExists.UnitaryGroupMassFormula.tT_tmul (τ : E →ₗ[F] F) (x : E) (b : Af F) :
    tT τ (x ⊗ₜ b) = algebraMap F (Af F) (τ x) * b := by sorry
