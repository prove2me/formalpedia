-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_embInf_succ
-- name    : Scott1972.ContinuousLattice.embInf_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:35.741871+00:00
-- url     : https://prove2.me/theorems/db9857d0-19b7-5b9b-8fa6-c7f8549b7ee3
-- title:
--   Continuous Lattice: emb Inf succ
-- statement:
--   **Scott 1972, §4 (recursion equation).** `i_{n∞} = i_{(n+1)∞} ∘ iₙ`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L534-L550
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L534-L550

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.embInf_succ (n : ℕ) (x : D n) :
    embInf D P (n + 1) ((P n).incl x) = embInf D P n x := by sorry
