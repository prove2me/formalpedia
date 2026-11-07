-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_anchored_degree_zero_interval
-- name    : QEC.Locality.WeightedConnectedSetMass.anchored_degree_zero_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:47:43.382665+00:00
-- url     : https://prove2.me/theorems/680c92e2-26d0-4d39-9643-9ff08b898efc
-- title:
--   Weighted Connected Set Mass: anchored degree zero interval
-- statement:
--   The Weighted Connected Set Mass construction uses the anchored degree zero interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L250-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L250-L255

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

theorem QEC.Locality.WeightedConnectedSetMass.anchored_degree_zero_interval (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}=0) (R : Finset V) (a : V → ℝ) (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U =
      if L≤1 ∧ 1≤U then ∑ r ∈ R, a r else 0 := by sorry
