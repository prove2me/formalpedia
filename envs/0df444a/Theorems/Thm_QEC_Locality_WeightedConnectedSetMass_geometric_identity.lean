-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_geometric_identity
-- name    : QEC.Locality.WeightedConnectedSetMass.geometric_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:58.524235+00:00
-- url     : https://prove2.me/theorems/7e6e9493-26bc-457b-a810-394d1caa68ef
-- title:
--   Weighted Connected Set Mass: geometric identity
-- statement:
--   Finite geometric identity proved algebraically, valid even at q=0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L258-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L258-L262

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

theorem QEC.Locality.WeightedConnectedSetMass.geometric_identity (q : ℝ) (n : ℕ) :
    (1-q)*(∑ j ∈ Finset.range n, q^j) = 1-q^n := by sorry
