-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_integral_smul_mul_eq_toReal_sub_3372cbe3807f
-- name    : P2M_GroundTheory_Heights__Heights_finsum_integral_smul_mul_eq_toReal_sub_3372cbe3807f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:00.09638+00:00
-- url     : https://prove2.me/theorems/5dffcc49-694b-4721-9f9f-49a8f02254c1
-- title:
--   P2 M Ground Theory Heights  Heights finsum integral smul mul eq to Real sub 3372cbe3807f: P2 M Ground Theory Heights  Heights finsum integral smul mul eq to Real sub 3372cbe3807f
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum integral smul mul eq to Real sub 3372cbe3807f construction uses the P2 M Ground Theory Heights  Heights finsum integral smul mul eq to Real sub 3372cbe3807f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L70-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L70-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder
variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem P2M_GroundTheory_Heights__Heights_finsum_integral_smul_mul_eq_toReal_sub_3372cbe3807f {f : E → ℝ} (hf : Measurable f) {T : Set W}
    (hT : T.Finite) (v : W → E) (ρ : W → ℂ → ℝ) (hρ : ∀ w t, 0 ≤ ρ w t)
    (hρc : ∀ w, Continuous (ρ w))
    (hp : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤)
    (hm : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤) :
    ∑ᶠ w ∈ T, ∫ t : ℂ, f (t • v w) * ρ w t =
      (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal -
        (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_integral_smul_mul_eq_toReal_sub» := P2M_GroundTheory_Heights__Heights_finsum_integral_smul_mul_eq_toReal_sub_3372cbe3807f
