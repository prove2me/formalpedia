-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_shape_flatMap
-- name    : PI.UnitaryGroupMassFormula.UsCompose.shape_flatMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:50:20.050547+00:00
-- url     : https://prove2.me/theorems/64f6a158-17bd-4003-a0a1-a5fc1a769a0e
-- title:
--   Us Compose: shape flat Map
-- statement:
--   The Us Compose construction uses the shape flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L164-L171

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryGroupMassFormula.UsCompose.shape_flatMap {k j ρ : ℕ} (F : Mat k (j + ρ) → E) (L : FS k (j + ρ))
    (f : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ)) → FS k (j + ρ)) (g : Mat k (j + ρ)) :
    shape k j ρ F (L.flatMap f) g = (L.map fun e => shape k j ρ F (f e) g).sum := by sorry
