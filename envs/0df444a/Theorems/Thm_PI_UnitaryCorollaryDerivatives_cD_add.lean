-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cD_add
-- name    : PI.UnitaryCorollaryDerivatives.cD_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:25.208797+00:00
-- url     : https://prove2.me/theorems/6257cd6f-51c9-4eb2-8f68-2d32cdaecf96
-- title:
--   Unitary Corollary Derivatives: c D add
-- statement:
--   The Unitary Corollary Derivatives construction uses the c D add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStarOf.lean#L24-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStarOf.lean#L24-L53

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

theorem PI.UnitaryCorollaryDerivatives.cD_add {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {F₁ F₂ : B.Mat k (j + ρ) → E} {C₁ C₂ c : ℝ}
    (h₁ : Good k j ρ Q A₁ O F₁ C₁ c) (h₂ : Good k j ρ Q A₁ O F₂ C₂ c) :
    Good k j ρ Q A₁ O (fun g => F₁ g + F₂ g) (C₁ + C₂) c := by sorry
