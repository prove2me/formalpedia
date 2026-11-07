-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_anchored_one_mass
-- name    : QEC.Locality.WeightedConnectedSetMass.anchored_one_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:23:09.409519+00:00
-- url     : https://prove2.me/theorems/550235aa-c7e9-473f-a592-f90092edae14
-- title:
--   Weighted Connected Set Mass: anchored one mass
-- statement:
--   The Weighted Connected Set Mass construction uses the anchored one mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L171-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L171-L177

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

theorem QEC.Locality.WeightedConnectedSetMass.anchored_one_mass (G : SimpleGraph V) (R : Finset V) (a : V → ℝ) :
    anchoredMass G R 1 a = ∑ r ∈ R, a r := by sorry
