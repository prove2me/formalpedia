-- Prove2me | Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_eq_biUnion
-- name    : QEC.Locality.ConnectedSetCounting.anchored_eq_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:12.37449+00:00
-- url     : https://prove2.me/theorems/8d990840-2567-4036-9e31-26042606d434
-- title:
--   Connected Set Counting: anchored eq bi Union
-- statement:
--   Exact union identity, with no disjointness premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L274-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L274-L283

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem QEC.Locality.ConnectedSetCounting.anchored_eq_biUnion (G : SimpleGraph V) (R : Finset V) (m : Nat) :
    anchored G R m = R.biUnion (fun r => rooted G r m) := by sorry
