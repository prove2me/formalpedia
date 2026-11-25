-- Prove2me | Theorems.Thm_SZ_isDigits_run_fst
-- name    : SZ.isDigits_run_fst
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:03:22.805862+00:00
-- url     : https://prove2.me/theorems/46d17c9d-0c76-433f-bf40-f1714e31a759
-- title:
--   SZ: is Digits run fst
-- statement:
--   The SZ construction uses the is Digits run fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L857-L861
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L857-L861

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.isDigits_run_fst {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (fun i => (d i).1) := by sorry
