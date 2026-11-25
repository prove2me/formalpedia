-- Prove2me | Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_of_homeo
-- name    : PI.VolStabW.SdTestInfW.testEx_of_homeo
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:09.250599+00:00
-- url     : https://prove2.me/theorems/b64ccad8-82be-4c84-a810-f7a53f7237a8
-- title:
--   Sd Test Inf W: test Ex of homeo
-- statement:
--   The Sd Test Inf W construction uses the test Ex of homeo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L208-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L208-L244

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

theorem PI.VolStabW.SdTestInfW.testEx_of_homeo {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : SdUniqW.TestEx μ χ := by sorry
