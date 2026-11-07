-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_one_mass
-- name    : QEC.Locality.WeightedConnectedSetMass.rooted_one_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:35.951614+00:00
-- url     : https://prove2.me/theorems/ad88ec27-f379-4a71-8c06-b6993066b753
-- title:
--   Weighted Connected Set Mass: rooted one mass
-- statement:
--   The Weighted Connected Set Mass construction uses the rooted one mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L157-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L157-L158

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

theorem QEC.Locality.WeightedConnectedSetMass.rooted_one_mass (G : SimpleGraph V) (r : V) (a : V → ℝ) :
    rootedMass G r 1 a = a r := by sorry
