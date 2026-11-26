-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_embInf_family_directed
-- name    : Scott1972.ContinuousLattice.embInf_family_directed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:11.909807+00:00
-- url     : https://prove2.me/theorems/6362da79-5570-4677-853a-9668d4c115be
-- title:
--   Continuous Lattice: emb Inf family directed
-- statement:
--   The Continuous Lattice construction uses the emb Inf family directed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L560-L562
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L560-L562

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.embInf_family_directed (x : InverseLimit D P) :
    DirectedOn (· ≤ ·) (Set.range (fun n => embInf D P n (x.1 n))) := by sorry
