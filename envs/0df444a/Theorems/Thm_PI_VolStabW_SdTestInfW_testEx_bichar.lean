-- Prove2me | Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_bichar
-- name    : PI.VolStabW.SdTestInfW.testEx_bichar
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:08.066045+00:00
-- url     : https://prove2.me/theorems/dd5e5516-f6b3-5fa5-87a0-99168cc90c74
-- title:
--   Sd Test Inf W: test Ex bichar
-- statement:
--   The Sd Test Inf W construction uses the test Ex bichar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L189-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L189-L206

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

theorem PI.VolStabW.SdTestInfW.testEx_bichar (μ : Measure W) [μ.IsAddHaarMeasure] {χ : W → W → ℂ} (h : IsBichar χ) :
    SdUniqW.TestEx μ χ := by sorry
