-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_shape_mul
-- name    : PI.UnitaryGroupMassFormula.UsCompose.shape_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:48.963724+00:00
-- url     : https://prove2.me/theorems/2e4608f0-9c25-407a-b912-9d7c03a245ee
-- title:
--   Us Compose: shape mul
-- statement:
--   The Us Compose construction uses the shape mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L155-L162

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

theorem PI.UnitaryGroupMassFormula.UsCompose.shape_mul {k j ρ : ℕ} (F : Mat k (j + ρ) → E) (s : SC (2 * (j + ρ) + k + 1)) (M : FS k (j + ρ))
    (g : Mat k (j + ρ)) :
    shape k j ρ F (M.map fun e => (mulSC s e.1, e.2)) g = sv k j ρ s g • shape k j ρ F M g := by sorry
