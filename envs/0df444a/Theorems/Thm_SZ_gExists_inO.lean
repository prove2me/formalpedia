-- Prove2me | Theorems.Thm_SZ_gExists_inO
-- name    : SZ.gExists_inO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:17:32.022895+00:00
-- url     : https://prove2.me/theorems/1025c5fa-5bd1-4970-aedb-389b17a558f9
-- title:
--   SZ: g Exists in O
-- statement:
--   **The play always reaches a branch point.**  Off `O` the offset is forced, and the
--   zone graph is `Z₂ → Z₂`, `Z₃ → Z₃`, `Z₁ ↛ Z₄`, `Z₄ ↛ Z₁`; so an orbit avoiding `O` is
--   eventually confined to a single zone and sits at its fixed point — `3`, `3√3`, `3 + 3√3`
--   or `0` — each excluded by the growth of the `√3`-coordinate.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L410-L537
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L410-L537

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gExists_inO {s : ℤ × ℤ} (h : GStart s) : ∃ k, InO (valS (gState s k)) := by sorry
