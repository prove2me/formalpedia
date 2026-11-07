-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_interval_strong
-- name    : QEC.Locality.WeightedConnectedSetMass.occupied_interval_strong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:23:13.005044+00:00
-- url     : https://prove2.me/theorems/cf3506ad-46f7-4c36-b6a8-e980623afb1b
-- title:
--   Weighted Connected Set Mass: occupied interval strong
-- statement:
--   The Weighted Connected Set Mass construction uses the occupied interval strong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L441-L477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L441-L477

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

theorem QEC.Locality.WeightedConnectedSetMass.occupied_interval_strong (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (hRB : Disjoint R B) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => occupiedMass G R B m a) L U ≤
      (R.card : ℝ)*structuralEnvelope (alpha Delta) b B.card L U := by sorry
