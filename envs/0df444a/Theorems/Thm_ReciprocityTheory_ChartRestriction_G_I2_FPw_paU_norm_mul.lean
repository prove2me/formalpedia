-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paU_norm_mul
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_norm_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:42.633069+00:00
-- url     : https://prove2.me/theorems/6778f294-553a-4c5e-80a5-a9ec890077da
-- title:
--   FPw: pa U norm mul
-- statement:
--   The FPw construction uses the pa U norm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L33-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L33-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_norm_mul (q : ℕ) (a v : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) :
    ‖paU q a F v‖ * paW q v = ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) *
      Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by sorry
