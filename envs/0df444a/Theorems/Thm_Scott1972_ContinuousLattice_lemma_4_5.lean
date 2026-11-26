-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_lemma_4_5
-- name    : Scott1972.ContinuousLattice.lemma_4_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:16.860389+00:00
-- url     : https://prove2.me/theorems/8111250f-a6ec-5b55-908d-eb604666b29a
-- title:
--   Continuous Lattice: lemma 4 5
-- statement:
--   **Scott 1972, Lemma 4.5.** A criterion for recognizing projections out of the limit: if a
--   sequence `u : ∀ n, D_{n+1}` satisfies the (shifted) recursion `j_{n+1}(u_{n+2}) = u_{n+1}`, then the
--   monotone limit `u_∞ = ⨆ₙ i_{(n+1)∞}(uₙ)` has `j_{∞(n+1)}(u_∞) = uₙ`.
--
--   The proof follows Scott's argument at source lines 1316–1320.  First the defining family is
--   monotone.  Continuity of `j_{∞(n+1)}` therefore moves the projection through its directed
--   supremum.  Finally, for every `m ≥ n`, the identity
--   `j_{∞(n+1)}(i_{(m+1)∞}(u_m)) = u_n` is proved by induction on `m - n`, peeling one projection with
--   `projLE_succ` and then applying the recursion hypothesis `j_{m+1}(u_{m+1}) = u_m`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L608-L663
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L608-L663

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.lemma_4_5 (u : ∀ n, D (n + 1))
    (hu : ∀ n, (P (n + 1)).retr (u (n + 1)) = u n) (n : ℕ) :
    (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P).1 (n + 1) = u n := by sorry
