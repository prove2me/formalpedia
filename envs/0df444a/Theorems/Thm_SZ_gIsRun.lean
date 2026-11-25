-- Prove2me | Theorems.Thm_SZ_gIsRun
-- name    : SZ.gIsRun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:33:17.410181+00:00
-- url     : https://prove2.me/theorems/b3fc0922-9b37-4a44-8b22-fbce2e302c9f
-- title:
--   SZ: g Is Run
-- statement:
--   The SZ construction uses the g Is Run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L190-L194
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L190-L194

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gIsRun {s : ℤ × ℤ} (h : GStart s) : IsRun s (gDigit s) := by sorry
