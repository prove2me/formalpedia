-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_bounds
-- name    : QEC.Locality.WeightedConnectedSetMass.rooted_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:28.058041+00:00
-- url     : https://prove2.me/theorems/307d8047-3e3b-480b-b271-bfa1bc2dc343
-- title:
--   Weighted Connected Set Mass: rooted bounds
-- statement:
--   No smallness or temperature sign is needed for a full-factor finite bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L113-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L113-L129

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem QEC.Locality.WeightedConnectedSetMass.rooted_bounds (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta)
    (r : V) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b) :
    0 ≤ rootedMass G r m a ∧ rootedMass G r m a ≤ (alpha Delta*b)^m := by sorry
