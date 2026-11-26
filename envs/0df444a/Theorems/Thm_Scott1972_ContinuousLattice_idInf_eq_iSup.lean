-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_idInf_eq_iSup
-- name    : Scott1972.ContinuousLattice.idInf_eq_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:34.26835+00:00
-- url     : https://prove2.me/theorems/44ded50c-e9ee-479b-b793-354228a08e61
-- title:
--   Continuous Lattice: id Inf eq i Sup
-- statement:
--   **Scott 1972, §4 (functional equation, "the remark following 4.2").** The identity of `D_∞` is
--   the directed lub of the approximating projections `rₙ = i_{n∞} ∘ j_{∞n}`:
--   `id = ⨆ₙ i_{n∞} ∘ j_{∞n}`. This is the algebraic identity at the heart of Theorem 4.4.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L589-L597
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L589-L597

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.idInf_eq_iSup :
    (ScottMap.idMap : ScottMap (InverseLimit D P) (InverseLimit D P))
      = ⨆ n, (embInf D P n).comp (projInf D P n) := by sorry
