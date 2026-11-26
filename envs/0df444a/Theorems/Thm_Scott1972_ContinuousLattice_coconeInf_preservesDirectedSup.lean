-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.coconeInf_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:13.871886+00:00
-- url     : https://prove2.me/theorems/dc23fb76-8702-4f18-8699-c42eec272f37
-- title:
--   Continuous Lattice: cocone Inf preserves Directed Sup
-- statement:
--   `f∞` is Scott-continuous: `f∞(⊔S) = ⊔ f∞(S)` for directed `S` (each `fₙ` is continuous and a
--   double `⨆` over `ℕ × S` commutes).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L718-L733
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L718-L733

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']

theorem Scott1972.ContinuousLattice.coconeInf_preservesDirectedSup (f : ∀ n, ScottMap (D n) D') :
    PreservesDirectedSup (coconeInf D P f) := by sorry
