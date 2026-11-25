-- Prove2me | Theorems.Thm_PI_AprimeInfW_ST_testEx_fourier
-- name    : PI.AprimeInfW.ST.testEx_fourier
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:50.413514+00:00
-- url     : https://prove2.me/theorems/b5ca3014-84fb-50f6-bdff-a4c00b421bb4
-- title:
--   ST: test Ex fourier
-- statement:
--   The ST construction uses the test Ex fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/SdTest.lean#L162-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/SdTest.lean#L162-L190

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdFurther_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_SdTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW PI.AprimeInfW.ST
open MeasureTheory
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem PI.AprimeInfW.ST.testEx_fourier (μ : Measure W) [μ.IsAddHaarMeasure] (A : W ≃L[ℝ] W) :
    TestExP μ (fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)) := by sorry
