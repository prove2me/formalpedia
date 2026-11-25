-- Prove2me | Theorems.Thm_SZ_gState_snd_lower
-- name    : SZ.gState_snd_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:14:45.617883+00:00
-- url     : https://prove2.me/theorems/479c1ce7-0d59-5841-9696-c6ecb56f5af0
-- title:
--   SZ: g State snd lower
-- statement:
--   The SZ construction uses the g State snd lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L196-L199
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L196-L199

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.gState_snd_lower {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    3 ^ k * (s.2 - 3) + 3 ≤ (gState s k).2 := by sorry
