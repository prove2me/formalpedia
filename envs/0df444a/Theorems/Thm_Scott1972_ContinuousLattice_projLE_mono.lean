-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_projLE_mono
-- name    : Scott1972.ContinuousLattice.projLE_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:11.03539+00:00
-- url     : https://prove2.me/theorems/18890618-7dbf-50b2-8e71-e0307b450187
-- title:
--   Continuous Lattice: proj LE mono
-- statement:
--   The Continuous Lattice construction uses the proj LE mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L336-L344
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L336-L344

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.projLE_mono {m n : ℕ} (h : m ≤ n) {x y : D n} (hxy : x ≤ y) :
    projLE D P h x ≤ projLE D P h y := by sorry
