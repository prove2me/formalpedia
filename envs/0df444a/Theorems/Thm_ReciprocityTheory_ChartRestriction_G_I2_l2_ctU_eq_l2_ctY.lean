-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2_ctU_eq_l2_ctY
-- name    : ReciprocityTheory.ChartRestriction.G.I2.l2_ctU_eq_l2_ctY
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:16.799803+00:00
-- url     : https://prove2.me/theorems/8376a00a-0319-48a7-a5aa-b2178c4d4895
-- title:
--   I2: l2 ct U eq l2 ct Y
-- statement:
--   The I2 construction uses the l2 ct U eq l2 ct Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean#L195-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean#L195-L201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.l2_ctU_eq_l2_ctY (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) :
    Y.l2 q (ctU q (-((1 / (q : ℂ)) • w)) F) = (ctY Y w).l2 q F := by sorry
