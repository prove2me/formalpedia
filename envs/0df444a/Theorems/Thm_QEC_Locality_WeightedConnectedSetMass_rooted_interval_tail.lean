-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_interval_tail
-- name    : QEC.Locality.WeightedConnectedSetMass.rooted_interval_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:01.003719+00:00
-- url     : https://prove2.me/theorems/a757ef2f-5f75-44bd-aa7c-1f24e976470c
-- title:
--   Weighted Connected Set Mass: rooted interval tail
-- statement:
--   The rooted finite geometric consequence, with the same complete quantifiers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L323-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L323-L333

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

theorem QEC.Locality.WeightedConnectedSetMass.rooted_interval_tail (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}≤Delta) (r : V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => rootedMass G r m a) L U ≤
      (alpha Delta*b)^(max 1 L)/(1-alpha Delta*b) := by sorry
