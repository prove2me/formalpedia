-- Prove2me | Theorems.Thm_SZ_runState_snd_lower
-- name    : SZ.runState_snd_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:46.909206+00:00
-- url     : https://prove2.me/theorems/5863c8d7-6a08-4cf3-b993-a1aab24708d8
-- title:
--   SZ: run State snd lower
-- statement:
--   **Growth of the `√3`-coordinate** along any play: only `bᵢ ≤ 2` is used, so this holds
--   for every admissible play and not merely for the rule's own orbit.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L112-L122
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L112-L122

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runState_snd_lower {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) (k : ℕ) :
    3 ^ k * (s₀.2 - 3) + 3 ≤ (runState s₀ d k).2 := by sorry
