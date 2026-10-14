-- Prove2me | Theorems.Thm_ThreeSumSharpTail_retained_tiles_cost
-- name    : ThreeSumSharpTail.retained_tiles_cost
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:20:20.159611+00:00
-- url     : https://prove2.me/theorems/e6820e04-c05a-4cda-b5b6-9f719509a14c
-- title:
--   Sharp-tail bound for the actual all-tiles routine step count
-- statement:
--   Bounds the published natural-number time function tAllTiles at L=cm and t=ceil(theta*m). The bound counts the lengths of the star-box lists actually traversed by the routine, uses their exact binomial enumeration formula, and applies the sharp normalized tail. The bound holds for every number of bands, with explicit constant 1600 and all loop overheads included. Tile-fit, encoding, compiler and reduction costs must still be composed before claiming the final word-RAM runtime.
-- source:
--   Yuxuan Xu, same manuscript, Sections 2.1 and 4, equations unrelaxed and boxcost; actual tTile/tAllTiles time functions from anthropics/formal-math 3sum-apsp, commit e1a4e6508154ea59f030480661590a9fe3018011, ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean and ThreeSumApsp/Spec/Sec4/Theorem30/StarBoxes.lean.

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSPSource_RemainingDefinitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.retained_tiles_cost (c m nB : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    (Light.Sec4.tAllTiles (c * m) m ⌈θ * (m : ℝ)⌉₊ nB : ℝ) ≤
      1600 * ((c : ℝ) * m + 1) *
        ((nB : ℝ) ^ 2 * (((m : ℝ) + 1) *
          ((ThreeSumSharpTail.boxCount c m 0 : ℝ) *
            (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
              Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) + 1)) +
          nB + 1) := by sorry
