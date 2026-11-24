-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_toFS
-- name    : PI.UnitaryGroupMassFormula.UsCompose.toFS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:30:47.025312+00:00
-- url     : https://prove2.me/theorems/839700f4-b346-4b84-a9f4-5b8c3ebf90c0
-- title:
--   Us Compose: to FS
-- statement:
--   The Us Compose construction uses the to FS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L100-L120

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

theorem PI.UnitaryGroupMassFormula.UsCompose.toFS {k j ρ o κ : ℕ} {Θ : DiffOp k (j + ρ) Wp Wq} (h : InDD k j ρ o κ Θ) :
    ∃ L : FS k (j + ρ), Bd k j ρ κ o L ∧ ∀ H g, opApply Θ H g = shape k j ρ H L g := by sorry
