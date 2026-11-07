-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_prefix_formula
-- name    : QEC.Locality.WeightedConnectedSetMass.prefix_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:24.369198+00:00
-- url     : https://prove2.me/theorems/eb0a81b6-f806-4afd-a1ed-0f6a59e63a9f
-- title:
--   Weighted Connected Set Mass: prefix formula
-- statement:
--   Closed low prefix handles A=1 without dividing by zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L534-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L534-L545

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

theorem QEC.Locality.WeightedConnectedSetMass.prefix_formula (A b : ℝ) (l n : ℕ) (hA : A≠1) :
    b*(∑ j ∈ Finset.range n, A^(l+j)) = b*A^l*(A^n-1)/(A-1) := by sorry
