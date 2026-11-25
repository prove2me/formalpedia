-- Prove2me | Theorems.Thm_SZ_runXi_mem
-- name    : SZ.runXi_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:38:19.368978+00:00
-- url     : https://prove2.me/theorems/ca7b5183-52e6-4a68-a81f-49c66a9616db
-- title:
--   SZ: run Xi mem
-- statement:
--   The SZ construction uses the run Xi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L940-L944
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L940-L944

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runXi_mem {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    4 / 3 ≤ runXi d ∧ runXi d ≤ 5 / 3 := by sorry
