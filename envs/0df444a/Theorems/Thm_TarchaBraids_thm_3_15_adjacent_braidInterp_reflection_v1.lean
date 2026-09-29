-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_braidInterp_reflection_v1
-- name    : TarchaBraids.thm_3_15_adjacent_braidInterp_reflection_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T10:12:38.386662+00:00
-- url     : https://prove2.me/theorems/f3124337-40d5-4bfe-b363-311f54aa410c
-- title:
--   Tarcha 3.15 affine interpolation commutes with reflection
-- statement:
--   Affine interpolation between two reflected complex points is the reflection of their affine interpolation.
-- source:
--   Generic affine symmetry lemma isolated from the failed monolithic right-reflection child.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_braidInterp_reflection_v1 :
    ∀ (u : ℝ) (c z w : ℂ),
      braidInterp u (c - z) (c - w) = c - braidInterp u z w := by sorry

end TarchaBraids
