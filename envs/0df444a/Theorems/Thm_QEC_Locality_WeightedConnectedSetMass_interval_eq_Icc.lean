-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_interval_eq_Icc
-- name    : QEC.Locality.WeightedConnectedSetMass.interval_eq_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:46:27.221932+00:00
-- url     : https://prove2.me/theorems/e7b20e52-0314-441b-bbf6-b83ea7c49c02
-- title:
--   Weighted Connected Set Mass: interval eq Icc
-- statement:
--   Including m0 changes no mass when the rooted/anchored zero family is empty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L75-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L75-L87

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

theorem QEC.Locality.WeightedConnectedSetMass.interval_eq_Icc (f : ℕ → ℝ) (hf : f 0=0) (L U : ℕ) :
    interval f L U=∑ m ∈ Finset.Icc L U, f m := by sorry
