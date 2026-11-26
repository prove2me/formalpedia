-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_embLE_succ_left
-- name    : Scott1972.ContinuousLattice.embLE_succ_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:13.207542+00:00
-- url     : https://prove2.me/theorems/acfcbfc5-616e-56d6-a69f-fdd2277d3661
-- title:
--   Continuous Lattice: emb LE succ left
-- statement:
--   The Continuous Lattice construction uses the emb LE succ left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L308-L311
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L308-L311

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.embLE_succ_left {n m : ℕ} (h1 : n ≤ m) (h2 : n + 1 ≤ m) (x : D n) :
    embLE D P h2 ((P n).incl x) = embLE D P h1 x := by sorry
