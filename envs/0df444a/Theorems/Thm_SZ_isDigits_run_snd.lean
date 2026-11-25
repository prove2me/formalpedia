-- Prove2me | Theorems.Thm_SZ_isDigits_run_snd
-- name    : SZ.isDigits_run_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:38:00.312695+00:00
-- url     : https://prove2.me/theorems/8f61f1fb-df84-5ee1-807e-d85be9b67e93
-- title:
--   SZ: is Digits run snd
-- statement:
--   The SZ construction uses the is Digits run snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L863-L867
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L863-L867

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.isDigits_run_snd {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (fun i => (d i).2) := by sorry
