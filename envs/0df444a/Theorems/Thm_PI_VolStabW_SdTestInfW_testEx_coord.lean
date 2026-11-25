-- Prove2me | Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_coord
-- name    : PI.VolStabW.SdTestInfW.testEx_coord
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:13.582168+00:00
-- url     : https://prove2.me/theorems/e5825051-d128-5392-a167-757ba09308b0
-- title:
--   Sd Test Inf W: test Ex coord
-- statement:
--   The Sd Test Inf W construction uses the test Ex coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L304-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdTestInf.lean#L304-L313

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
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW

theorem PI.VolStabW.SdTestInfW.testEx_coord {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    {n : ℕ} (e : V ≃ₜ (Fin n → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : TestEx μ χ := by sorry
