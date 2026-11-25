-- Prove2me | Theorems.Thm_SZ_zones_of_not_InO
-- name    : SZ.zones_of_not_InO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:17:00.26834+00:00
-- url     : https://prove2.me/theorems/bf01ef17-48aa-419a-80bc-7cfc7701beb9
-- title:
--   SZ: zones of not In O
-- statement:
--   Off `O` the window `[0, 3U]` splits into the four forced zones.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L390-L404
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L390-L404

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.zones_of_not_InO {w : ℝ} (hO : ¬ InO w) :
    w < 2 ∨ (1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3) ∨
      (3 + Real.sqrt 3 < w ∧ w < 2 + 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < w := by sorry
