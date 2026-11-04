-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverUniformProjection_mixedFiber_uniform_card_le
-- name    : ThreeSum.TernaryCoverUniformProjection.mixedFiber_uniform_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:16.135658+00:00
-- url     : https://prove2.me/theorems/f025f7e2-a5b9-4485-9209-843537b87765
-- title:
--   Ternary Cover Uniform Projection: mixed Fiber uniform card le
-- statement:
--   Uniform full-word scalar projection cap for the actual trinary edge graph.
--   All combinatorial premises are discharged except the explicit prime-size
--   and difference-binomial inequalities.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformProjection.lean#L143-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverUniformProjection.lean#L143-L170

import Definitions.Def_Submission_ThreeSum_TernaryCoverGenericProjection
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverUniformProjection
open Finset TernaryJointType TernaryCoverLocal TernaryCoverGenericProjection
open TernaryCoverRegularity TernaryCoverOutputCap TernaryCoverProjection TernaryTypeLowerBound
variable {L p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryCoverUniformProjection.mixedFiber_uniform_card_le (α π : DigitType)
    (hthirds : π 2 = 3*α 2) (htotal : π 0+π 1+π 2 = L)
    (hspace : 2*(π 1)+3*(π 2) ≤ L) (hp : 4 < p)
    (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ p^2)
    (hchoose : L.choose (π 2/3) ≤ p) {a b : ZMod p} (hab : a ≠ 0 ∨ b ≠ 0)
    (q : Fin L → ZMod p) : (mixedFiber α π a b q).card ≤ p := by sorry
