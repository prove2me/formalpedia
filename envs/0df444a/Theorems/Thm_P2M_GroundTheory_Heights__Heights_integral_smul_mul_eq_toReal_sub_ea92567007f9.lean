-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_smul_mul_eq_toReal_sub_ea92567007f9
-- name    : P2M_GroundTheory_Heights__Heights_integral_smul_mul_eq_toReal_sub_ea92567007f9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:32.96651+00:00
-- url     : https://prove2.me/theorems/331c7854-5ff1-5d86-a9d0-e0a9774d3b9e
-- title:
--   P2 M Ground Theory Heights  Heights integral smul mul eq to Real sub ea92567007f9: P2 M Ground Theory Heights  Heights integral smul mul eq to Real sub ea92567007f9
-- statement:
--   The P2 M Ground Theory Heights  Heights integral smul mul eq to Real sub ea92567007f9 construction uses the P2 M Ground Theory Heights  Heights integral smul mul eq to Real sub ea92567007f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L44-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L44-L68

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

theorem P2M_GroundTheory_Heights__Heights_integral_smul_mul_eq_toReal_sub_ea92567007f9 {f : E → ℝ} (hf : Measurable f) (v : E) {ρ : ℂ → ℝ}
    (hρ : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ)
    (hp : ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤)
    (hm : ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤) :
    ∫ t : ℂ, f (t • v) * ρ t =
      (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)).toReal -
        (∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)).toReal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_smul_mul_eq_toReal_sub» := P2M_GroundTheory_Heights__Heights_integral_smul_mul_eq_toReal_sub_ea92567007f9
