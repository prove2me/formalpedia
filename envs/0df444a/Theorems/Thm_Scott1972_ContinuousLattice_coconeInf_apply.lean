-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_apply
-- name    : Scott1972.ContinuousLattice.coconeInf_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:25.202427+00:00
-- url     : https://prove2.me/theorems/b8b95a23-25b1-51f5-9397-09f6a98277a5
-- title:
--   Continuous Lattice: cocone Inf apply
-- statement:
--   The Continuous Lattice construction uses the cocone Inf apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L676-L677
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L676-L677

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

theorem Scott1972.ContinuousLattice.coconeInf_apply (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) :
    coconeInf D P f x = ⨆ n, f n (x.1 n) := by sorry
