-- Prove2me | Theorems.Thm_Sendov_B26_27_P_pos
-- name    : Sendov.B26_27.P_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:11.745527+00:00
-- url     : https://prove2.me/theorems/20e9664b-8d25-4cc3-93e5-01938a2e404d
-- title:
--   B26 27: P pos
-- statement:
--   The certificate: `17 ^ 24 * P α` is a positive combination of `αʲ (17-α)^(24-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L88-L149
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L88-L149

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
set_option maxHeartbeats 2000000

theorem Sendov.B26_27.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 13) :
    0 < 750669183453805732727050781250 + 3020533706655215263366699218750 * α + 5564839729610338783264160156250 * α ^ 2 + 6204652935907732786560058593750 * α ^ 3 + 4659850847351595430480957031250 * α ^ 4 + 2480313988118708551463378906250 * α ^ 5 + 956953438533800725637460937500 * α ^ 6 + 267988469385291406396875000000 * α ^ 7 + 53061280626889862612388984375 * α ^ 8 + 6649776660279075672227540625 * α ^ 9 + 67029306131497703210255025 * α ^ 10 - 797547671168471728584421521 * α ^ 11 + 69793209950586805764791132 * α ^ 12 + 1582701213221515173844854 * α ^ 13 + 64909025019891545058702 * α ^ 14 - 1621590589357829572680 * α ^ 15 - 347824272218530328424 * α ^ 16 - 21365270620680629952 * α ^ 17 - 794207858493279744 * α ^ 18 - 20077534583212032 * α ^ 19 - 355351304655360 * α ^ 20 - 4364532094464 * α ^ 21 - 35609836032 * α ^ 22 - 174127104 * α ^ 23 - 387072 * α ^ 24 := by sorry
