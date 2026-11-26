-- Prove2me | Theorems.Thm_Sendov_P_twenty_pos
-- name    : Sendov.P_twenty_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:58.476808+00:00
-- url     : https://prove2.me/theorems/ec42c46f-6997-5cf0-95ff-c68453b48291
-- title:
--   Sendov: P twenty pos
-- statement:
--   The Bernstein certificate for the degree-twenty numerator on `[0, 19/2]`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L53-L111
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L53-L111

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.P_twenty_pos (hα : 0 ≤ α) (hle : α ≤ 19 / 2) :
    0 <     2428684725423666483774 + 7331467129251995458872 * α + 9806391760574638480284 * α ^ 2 +
      7611575747798170524888 * α ^ 3 + 3758723770378675135797 * α ^ 4 + 1206125979814312523496 * α
      ^ 5 + 235504051379657180694 * α ^ 6 + 11454730616615814828 * α ^ 7 - 32607895082957507571 *
      α ^ 8 + 5227920728232680812 * α ^ 9 + 102472476340054572 * α ^ 10 - 2640164743526400 * α ^
      11 - 847605280292160 * α ^ 12 - 61937116512768 * α ^ 13 - 2508597900288 * α ^ 14 -
      62979502080 * α ^ 15 - 979335936 * α ^ 16 - 8690688 * α ^ 17 - 33792 * α ^ 18 := by sorry
