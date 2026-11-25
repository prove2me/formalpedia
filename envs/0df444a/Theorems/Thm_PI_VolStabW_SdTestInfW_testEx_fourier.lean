-- Prove2me | Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_fourier
-- name    : PI.VolStabW.SdTestInfW.testEx_fourier
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:22.801097+00:00
-- url     : https://prove2.me/theorems/ff9dd754-885a-4bbf-a99f-3ca053852cde
-- title:
--   Sd Test Inf W: test Ex fourier
-- statement:
--   The Sd Test Inf W construction uses the test Ex fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L159-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L159-L187

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem PI.VolStabW.SdTestInfW.testEx_fourier (μ : Measure W) [μ.IsAddHaarMeasure] (A : W ≃L[ℝ] W) :
    SdUniqW.TestEx μ (fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)) := by sorry
