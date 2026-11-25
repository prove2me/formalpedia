-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_neg_left
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_neg_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:43.438853+00:00
-- url     : https://prove2.me/theorems/cdc91309-1aad-57df-8e64-01b3474e798e
-- title:
--   FPw: Hf neg left
-- statement:
--   The FPw construction uses the Hf neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/HfNegRight.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/HfNegRight.lean#L20-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
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

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_neg_left (x z : EuclideanSpace ℂ ι) : Hf (-x) z = -Hf x z := by sorry
