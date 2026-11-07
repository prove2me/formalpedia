-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_singleton_interval
-- name    : QEC.Locality.WeightedConnectedSetMass.singleton_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:16:01.875483+00:00
-- url     : https://prove2.me/theorems/a9b920d2-296c-4d5e-a64b-a2d4d6802668
-- title:
--   Weighted Connected Set Mass: singleton interval
-- statement:
--   A degree-zero interval contains exactly its singleton mass when size1 is present.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L233-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L233-L242

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

theorem QEC.Locality.WeightedConnectedSetMass.singleton_interval (x : ℝ) (L U : ℕ) :
    interval (fun m => if m=1 then x else 0) L U =
      if L≤1 ∧ 1≤U then x else 0 := by sorry
