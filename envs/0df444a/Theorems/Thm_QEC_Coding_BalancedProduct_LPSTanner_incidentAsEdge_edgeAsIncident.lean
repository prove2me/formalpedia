-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentAsEdge_edgeAsIncident
-- name    : QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:19.035652+00:00
-- url     : https://prove2.me/theorems/0da67810-d347-44f7-851b-8269f6240ef4
-- title:
--   LPSTanner: incident As Edge edge As Incident
-- statement:
--   The LPSTanner construction uses the incident As Edge edge As Incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L245-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L245-L251

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype

theorem QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    incidentAsEdge q hq (edgeAsIncident q hq e g hg) = e := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
