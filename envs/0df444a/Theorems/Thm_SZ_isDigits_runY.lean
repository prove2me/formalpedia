-- Prove2me | Theorems.Thm_SZ_isDigits_runY
-- name    : SZ.isDigits_runY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:20:22.356582+00:00
-- url     : https://prove2.me/theorems/480e7f60-6587-459d-ba8b-6b9053259431
-- title:
--   SZ: is Digits run Y
-- statement:
--   The SZ construction uses the is Digits run Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L920-L924
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L920-L924

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.isDigits_runY {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (runY d) := by sorry
