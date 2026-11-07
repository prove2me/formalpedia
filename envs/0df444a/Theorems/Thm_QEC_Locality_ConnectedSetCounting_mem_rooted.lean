-- Prove2me | Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_rooted
-- name    : QEC.Locality.ConnectedSetCounting.mem_rooted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:05.609951+00:00
-- url     : https://prove2.me/theorems/268f2c13-f356-4770-9618-4b6817d12795
-- title:
--   Connected Set Counting: mem rooted
-- statement:
--   The Connected Set Counting construction uses the mem rooted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L244-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L244-L247

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

theorem QEC.Locality.ConnectedSetCounting.mem_rooted (G : SimpleGraph V) (r : V) (m : Nat) (A : Finset V) :
    A ∈ rooted G r m ↔ r ∈ A ∧ A.card = m ∧ (G.induce (A : Set V)).Connected := by sorry
