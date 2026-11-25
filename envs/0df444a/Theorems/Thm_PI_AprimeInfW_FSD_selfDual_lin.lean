-- Prove2me | Theorems.Thm_PI_AprimeInfW_FSD_selfDual_lin
-- name    : PI.AprimeInfW.FSD.selfDual_lin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:57.585448+00:00
-- url     : https://prove2.me/theorems/b5b6f4d4-534d-469f-ad83-006342a02911
-- title:
--   FSD: self Dual lin
-- statement:
--   The FSD construction uses the self Dual lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/FourierSD.lean#L14-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/FourierSD.lean#L14-L82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_FourierSD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW PI.AprimeInfW.FSD
open MeasureTheory Real Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped FourierTransform RealInnerProductSpace
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem PI.AprimeInfW.FSD.selfDual_lin (A : V ≃L[ℝ] V) (hA : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫) :
    SelfDual (ENNReal.ofReal (Real.sqrt |LinearMap.det (A : V →ₗ[ℝ] V)|) • (volume : Measure V))
      (fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) := by sorry
