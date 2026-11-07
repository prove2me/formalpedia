-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_one
-- name    : QEC.Locality.WeightedConnectedSetMass.occupied_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:13.563328+00:00
-- url     : https://prove2.me/theorems/1469febf-df4a-46cc-be16-ea6c56011489
-- title:
--   Weighted Connected Set Mass: occupied one
-- statement:
--   Exact singleton occupied mass, because anchors are disjoint from structural nodes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L351-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L351-L367

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

theorem QEC.Locality.WeightedConnectedSetMass.occupied_one (G : SimpleGraph V) (R B : Finset V) (hRB : Disjoint R B)
    (a : V → ℝ) : occupiedMass G R B 1 a=∑ r ∈ R, a r := by sorry
