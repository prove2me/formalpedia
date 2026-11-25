-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_bd_steps
-- name    : PI.UnitaryGroupMassFormula.UsCompose.bd_steps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:42:50.658797+00:00
-- url     : https://prove2.me/theorems/11d73cee-8186-4742-809f-c3b86bd94fba
-- title:
--   Us Compose: bd steps
-- statement:
--   The Us Compose construction uses the bd steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L58-L66

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

theorem PI.UnitaryGroupMassFormula.UsCompose.bd_steps (hP : DegDP) (hD : DegD) {k j ρ κ ℓ : ℕ} {w : List (Mat k (j + ρ))}
    (hw : ∀ X ∈ w, inLie k (j + ρ) X) {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (κ + j * w.length) (ℓ + w.length) (steps k j ρ w L) := by sorry
