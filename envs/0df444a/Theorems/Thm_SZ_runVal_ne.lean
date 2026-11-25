-- Prove2me | Theorems.Thm_SZ_runVal_ne
-- name    : SZ.runVal_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:15:32.506587+00:00
-- url     : https://prove2.me/theorems/590cae02-5963-4244-ae29-9db9ceb5b1b6
-- title:
--   SZ: run Val ne
-- statement:
--   Consequence: no state of a play started with `s₀.2 ≥ 4` is one of the trap fixed
--   points `0`, `3`, `3√3`, `3 + 3√3` — all of which have `√3`-coordinate at most `3`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L126-L136
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L126-L136

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.runVal_ne {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) (hq : 4 ≤ s₀.2)
    (k : ℕ) {p q : ℤ} (hqle : q ≤ 3) :
    valS (runState s₀ d k) ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by sorry
