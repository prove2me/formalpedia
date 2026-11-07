-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_degree_zero_mass
-- name    : QEC.Locality.WeightedConnectedSetMass.rooted_degree_zero_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:39.044526+00:00
-- url     : https://prove2.me/theorems/0c579fa1-6d30-4789-bf33-f39c6950e629
-- title:
--   Weighted Connected Set Mass: rooted degree zero mass
-- statement:
--   The Weighted Connected Set Mass construction uses the rooted degree zero mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L211-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L211-L216

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

theorem QEC.Locality.WeightedConnectedSetMass.rooted_degree_zero_mass (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} = 0) (r : V) (m : ℕ) (a : V → ℝ) :
    rootedMass G r m a = if m=1 then a r else 0 := by sorry
