-- Prove2me | Theorems.Thm_Sendov_B24_26_P_pos
-- name    : Sendov.B24_26.P_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:57.597533+00:00
-- url     : https://prove2.me/theorems/d0afd1b9-d46a-5c60-bff5-2c2ba81de19b
-- title:
--   B24 26: P pos
-- statement:
--   The certificate: `17 ^ 22 * P α` is a positive combination of `αʲ (17-α)^(22-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L88-L145
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L88-L145

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
set_option maxHeartbeats 2000000

theorem Sendov.B24_26.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 25 / 2) :
    0 < 874071004010582953643568750 + 3221297610086019399669004500 * α + 5386914463346812349691460974 * α ^ 2 + 5391225879978445091101054368 * α ^ 3 + 3582299145670361769507272658 * α ^ 4 + 1654127651781089540379647100 * α ^ 5 + 537462463626302644652842710 * α ^ 6 + 120043033655516749475390448 * α ^ 7 + 16184849120135434020794931 * α ^ 8 - 222784389930881498880726 * α ^ 9 - 2725770297915674501126913 * α ^ 10 + 248640476833385673099320 * α ^ 11 + 6386094327528944247792 * α ^ 12 + 230085309479261626272 * α ^ 13 - 10099884196228450032 * α ^ 14 - 1569527054513950464 * α ^ 15 - 87896838917715456 * α ^ 16 - 2989402709094912 * α ^ 17 - 67703370254592 * α ^ 18 - 1033617561600 * α ^ 19 - 10281172992 * α ^ 20 - 60432384 * α ^ 21 - 159744 * α ^ 22 := by sorry
