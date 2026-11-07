-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_structuralEnvelope_formula
-- name    : QEC.Locality.WeightedConnectedSetMass.structuralEnvelope_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:48:16.849387+00:00
-- url     : https://prove2.me/theorems/3459f59f-d7ae-4dd8-8dbd-fac5368aafe8
-- title:
--   Weighted Connected Set Mass: structural Envelope formula
-- statement:
--   The complete split is a finite prefix plus a geometric shifted tail at every cutoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L498-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L498-L531

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

theorem QEC.Locality.WeightedConnectedSetMass.structuralEnvelope_formula (A b : ℝ) (c L U : ℕ) :
    structuralEnvelope A b c L U =
      b*geometric A (max 1 L) (min (U+1-max 1 L) (c+1-max 1 L)) +
      A^c*geometric (A*b) (max (max 1 L) (c+1)-c)
        (U+1-max (max 1 L) (c+1)) := by sorry
