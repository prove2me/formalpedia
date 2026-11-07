-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_degree_zero_interval
-- name    : QEC.Locality.WeightedConnectedSetMass.rooted_degree_zero_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:47:41.606235+00:00
-- url     : https://prove2.me/theorems/bb9e68c6-434d-492b-9366-0b3bf141b34e
-- title:
--   Weighted Connected Set Mass: rooted degree zero interval
-- statement:
--   The Weighted Connected Set Mass construction uses the rooted degree zero interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L244-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L244-L248

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

theorem QEC.Locality.WeightedConnectedSetMass.rooted_degree_zero_interval (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}=0) (r : V) (a : V → ℝ) (L U : ℕ) :
    interval (fun m => rootedMass G r m a) L U = if L≤1 ∧ 1≤U then a r else 0 := by sorry
