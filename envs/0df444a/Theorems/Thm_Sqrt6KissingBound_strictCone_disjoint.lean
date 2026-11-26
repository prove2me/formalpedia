-- Prove2me | Theorems.Thm_Sqrt6KissingBound_strictCone_disjoint
-- name    : Sqrt6KissingBound.strictCone_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:55.804805+00:00
-- url     : https://prove2.me/theorems/aea92df4-5532-55cf-8ad0-396244ba7719
-- title:
--   Sqrt6 Kissing Bound: strict Cone disjoint
-- statement:
--   Two `π/6` cones about unit vectors with inner product at most `1/2` are disjoint.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Geometry.lean#L39-L128
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Geometry.lean#L39-L128

import Mathlib
import Definitions.Def_Sqrt6KissingBound_Geometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Sqrt6KissingBound.strictCone_disjoint {x z : E}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (strictCone x) (strictCone z) := by sorry
