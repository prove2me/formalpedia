-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_strong
-- name    : QEC.Locality.WeightedConnectedSetMass.occupied_strong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:23:09.999918+00:00
-- url     : https://prove2.me/theorems/972a3c29-5ea7-4559-a9a4-875da43385e6
-- title:
--   Weighted Connected Set Mass: occupied strong
-- statement:
--   Explicit q<1 is needed to lower the actual number of occupied factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L413-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L413-L432

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

theorem QEC.Locality.WeightedConnectedSetMass.occupied_strong (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (hRB : Disjoint R B) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1) :
    occupiedMass G R B m a ≤ (R.card : ℝ)*alpha Delta^m*b^(max 1 (m-B.card)) := by sorry
