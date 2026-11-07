-- Prove2me | Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_anchored_interval_tail
-- name    : QEC.Locality.WeightedConnectedSetMass.anchored_interval_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:47:55.189943+00:00
-- url     : https://prove2.me/theorems/cbad5bb9-981d-4efe-982d-b58f5cfdc01e
-- title:
--   Weighted Connected Set Mass: anchored interval tail
-- statement:
--   The Weighted Connected Set Mass construction uses the anchored interval tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L306-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean#L306-L320

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

theorem QEC.Locality.WeightedConnectedSetMass.anchored_interval_tail (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R : Finset V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U ≤
      (R.card : ℝ)*(alpha Delta*b)^(max 1 L)/(1-alpha Delta*b) := by sorry
