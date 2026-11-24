-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mkTerm_word
-- name    : PI.UnitaryGroupMassFormula.UsCompose.mkTerm_word
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:31:03.36882+00:00
-- url     : https://prove2.me/theorems/a0deca0e-ed42-4972-900a-acb422d83535
-- title:
--   Us Compose: mk Term word
-- statement:
--   The Us Compose construction uses the mk Term word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L93-L98

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem PI.UnitaryGroupMassFormula.UsCompose.mkTerm_word {k j ρ : ℕ} {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))}
    (h : ∀ X ∈ e.2, inLie k (j + ρ) X) : (mkTerm (Wp := Wp) (Wq := Wq) k j ρ e).word = e.2 := by sorry
