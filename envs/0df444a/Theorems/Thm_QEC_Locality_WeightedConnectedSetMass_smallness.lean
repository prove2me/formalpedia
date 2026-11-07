-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_smallness
-- name    : QEC.Locality.WeightedConnectedSetMass.smallness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:59.829563+00:00
-- url     : https://prove2.me/theorems/46ffff96-8080-4e72-8c49-8c909d405b4a
-- title:
--   Weighted Connected Set Mass: smallness
-- statement:
--   Smallness derives the decreasing-power domain; it is never assumed silently.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L336-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L336-L342

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

theorem QEC.Locality.WeightedConnectedSetMass.smallness (Delta : ℕ) (b : ℝ) (hb : 0≤b) (hq : alpha Delta*b<1) :
    0≤b ∧ b≤alpha Delta*b ∧ b<1 := by sorry
