-- Prove2me | Theorems.Thm_QEC_Locality_ConnectedSetCounting_rooted_one
-- name    : QEC.Locality.ConnectedSetCounting.rooted_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:31.319345+00:00
-- url     : https://prove2.me/theorems/644664d4-cd1b-4d19-b2fd-7ffe37160afb
-- title:
--   Connected Set Counting: rooted one
-- statement:
--   The singleton is connected for every graph; no edge premise is needed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L309-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/ConnectedSetCounting.lean#L309-L328

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

theorem QEC.Locality.ConnectedSetCounting.rooted_one (G : SimpleGraph V) (r : V) : rooted G r 1 = {{r}} := by sorry
