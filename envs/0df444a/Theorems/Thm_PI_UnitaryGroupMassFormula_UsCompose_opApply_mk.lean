-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_opApply_mk
-- name    : PI.UnitaryGroupMassFormula.UsCompose.opApply_mk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:31:19.016788+00:00
-- url     : https://prove2.me/theorems/718bcd6a-5f11-44ef-b377-47a514babc08
-- title:
--   Us Compose: op Apply mk
-- statement:
--   The Us Compose construction uses the op Apply mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L122-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L122-L134

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

theorem PI.UnitaryGroupMassFormula.UsCompose.opApply_mk {k j ρ : ℕ} (L : FS k (j + ρ)) (hL : ∀ e ∈ L, ∀ X ∈ e.2, inLie k (j + ρ) X)
    (F : Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (g : Mat k (j + ρ)) :
    opApply (L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ)) F g = shape k j ρ F L g := by sorry
