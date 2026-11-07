-- Prove2me | Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_anchored
-- name    : QEC.Locality.ConnectedSetCounting.mem_anchored
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:14.782903+00:00
-- url     : https://prove2.me/theorems/2389a34b-0df2-4e95-9ed4-5683b8e90062
-- title:
--   Connected Set Counting: mem anchored
-- statement:
--   The Connected Set Counting construction uses the mem anchored property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L267-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L267-L271

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

theorem QEC.Locality.ConnectedSetCounting.mem_anchored (G : SimpleGraph V) (R : Finset V) (m : Nat) (A : Finset V) :
    A ∈ anchored G R m ↔ A.card = m ∧
      (G.induce (A : Set V)).Connected ∧ (A ∩ R).Nonempty := by sorry
