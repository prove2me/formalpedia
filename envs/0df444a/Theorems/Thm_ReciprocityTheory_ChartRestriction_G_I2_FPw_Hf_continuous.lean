-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_continuous
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_continuous
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:36.482812+00:00
-- url     : https://prove2.me/theorems/d677d761-adb6-5705-8efc-137a0510d495
-- title:
--   FPw: Hf continuous
-- statement:
--   The FPw construction uses the Hf continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L23-L25

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

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_continuous (a : EuclideanSpace ℂ ι) : Continuous fun v : EuclideanSpace ℂ ι => Hf v a := by sorry
