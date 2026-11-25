-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cD_delta
-- name    : PI.UnitaryCorollaryDerivatives.cD_delta
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:41.885912+00:00
-- url     : https://prove2.me/theorems/574b7546-5420-472e-8fff-6c31696e76c4
-- title:
--   Unitary Corollary Derivatives: c D delta
-- statement:
--   The Unitary Corollary Derivatives construction uses the c D delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStarOf.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStarOf.lean#L76-L83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStarOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryCorollaryDerivatives.cD_delta {χ : ℂ → ℂ} (hχ : IsCutC χ) : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport χ, δ ≤ ‖z‖ := by sorry
