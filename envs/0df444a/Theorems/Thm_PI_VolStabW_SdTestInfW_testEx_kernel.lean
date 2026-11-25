-- Prove2me | Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_kernel
-- name    : PI.VolStabW.SdTestInfW.testEx_kernel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:32.450275+00:00
-- url     : https://prove2.me/theorems/75ee27dd-f3f0-4585-8ad3-6c7d81e0936f
-- title:
--   Sd Test Inf W: test Ex kernel
-- statement:
--   The Sd Test Inf W construction uses the test Ex kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L131-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L131-L157

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

theorem PI.VolStabW.SdTestInfW.testEx_kernel (μ : Measure W) [μ.IsAddHaarMeasure] (χ : W → W → ℂ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hc : ∀ y, Continuous fun x => χ x y)
    (t : W) (ht0 : t ≠ 0) (ht : ∀ y, χ t y = 1) : SdUniqW.TestEx μ χ := by sorry
