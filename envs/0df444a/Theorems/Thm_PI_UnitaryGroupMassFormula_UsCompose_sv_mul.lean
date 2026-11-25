-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_sv_mul
-- name    : PI.UnitaryGroupMassFormula.UsCompose.sv_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:02.296456+00:00
-- url     : https://prove2.me/theorems/ed33d9b2-a75f-523e-bdca-e68a570baf33
-- title:
--   Us Compose: sv mul
-- statement:
--   The Us Compose construction uses the sv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L146-L149

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

theorem PI.UnitaryGroupMassFormula.UsCompose.sv_mul {k j ρ : ℕ} (s t : SC (2 * (j + ρ) + k + 1)) (g : Mat k (j + ρ)) :
    sv k j ρ (mulSC s t) g = sv k j ρ s g * sv k j ρ t g := by sorry
