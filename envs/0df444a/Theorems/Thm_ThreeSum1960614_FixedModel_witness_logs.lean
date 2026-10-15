-- Prove2me | Theorems.Thm_ThreeSum1960614_FixedModel_witness_logs
-- name    : ThreeSum1960614.FixedModel.witness_logs
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T13:34:46.008424+00:00
-- url     : https://prove2.me/theorems/18279722-8cec-48a0-97f0-d0162d84f3d2
-- title:
--   Six exact logarithmic intervals at the model witnesses
-- statement:
--   Fix
--   $$s=\frac{252561863698173}{6250000000000000},\qquad u=\frac{859960785302793}{5000000000000000}.$$
--   For the six positive rational arguments
--   $$32s,\quad2(1-s),\quad1+s/231,\quad8u,\quad2(1-u),\quad1+u/231,$$
--   the natural logarithm lies in each corresponding exact closed rational interval stated in the theorem. All endpoints are fixed rationals; the intervals have width $10^{-22}$. There are no numerical-oracle or rounding hypotheses. These enclosures supply the split-point entropy and collision bounds and the ratio witness used in the model lower bound.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ModelWitnessLogs.lean#L36-L61

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_FixedModelAlgebra
import Definitions.Def_ThreeSum1960614_ModelWitnessPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped BigOperators

open ThreeSum1960614 ThreeSum1960614.FixedModel

theorem ThreeSum1960614.FixedModel.witness_logs :
    ((1285276917605861577967/5000000000000000000000 : ℝ) ≤ Real.log (32*split) ∧
      Real.log (32*split) ≤ (514110767042344631187/2000000000000000000000 : ℝ)) ∧
    ((6518981175759055705591/10000000000000000000000 : ℝ) ≤ Real.log (2*(1-split)) ∧
      Real.log (2*(1-split)) ≤ (814872646969881963199/1250000000000000000000 : ℝ)) ∧
    ((437298312323441179/2500000000000000000000 : ℝ) ≤ Real.log (1+split/231) ∧
      Real.log (1+split/231) ≤ (1749193249293764717/10000000000000000000000 : ℝ)) ∧
    ((638270279972769945753/2000000000000000000000 : ℝ) ≤ Real.log (8*ratioPoint) ∧
      Real.log (8*ratioPoint) ≤ (1595675699931924864383/5000000000000000000000 : ℝ)) ∧
    ((1008829056134582490741/2000000000000000000000 : ℝ) ≤ Real.log (2*(1-ratioPoint)) ∧
      Real.log (2*(1-ratioPoint)) ≤ (2522072640336456226853/5000000000000000000000 : ℝ)) ∧
    ((58146699145150531/78125000000000000000 : ℝ) ≤ Real.log (1+ratioPoint/231) ∧
      Real.log (1+ratioPoint/231) ≤ (7442777490579267969/10000000000000000000000 : ℝ)) := by sorry
