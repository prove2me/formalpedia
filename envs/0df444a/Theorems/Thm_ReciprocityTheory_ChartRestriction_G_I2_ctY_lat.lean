-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ctY_lat
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ctY_lat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:24.908806+00:00
-- url     : https://prove2.me/theorems/960a7b74-197b-4306-b683-264403f3efd4
-- title:
--   I2: ct Y lat
-- statement:
--   The I2 construction uses the ct Y lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean#L27-L27

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ctY_lat (Y : GT ι) (w : EuclideanSpace ℂ ι) : lat (ctY Y w).b = lat Y.b := by sorry
