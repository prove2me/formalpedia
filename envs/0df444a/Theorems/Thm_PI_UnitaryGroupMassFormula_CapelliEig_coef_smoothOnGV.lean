-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_coef_smoothOnGV
-- name    : PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:49:01.529554+00:00
-- url     : https://prove2.me/theorems/43829f67-1909-4bc1-9212-0c3814c97769
-- title:
--   Capelli Eig: coef smooth On GV
-- statement:
--   The Capelli Eig construction uses the coef smooth On GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CapelliEigenvalues/Smooth.lean#L43-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CapelliEigenvalues/Smooth.lean#L43-L66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CapelliEig
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV {n : ℕ} (ε : Fin n → Bool) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (τ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs)
    (hQ : ∀ w, Formalism.REAL.SmoothOnGV ε (fun x => τ x (Q w))) :
    Formalism.REAL.SmoothOnGV ε (fun x => P.comp ((τ x).comp Q)) := by sorry
