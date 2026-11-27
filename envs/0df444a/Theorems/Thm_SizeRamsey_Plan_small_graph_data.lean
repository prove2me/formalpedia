-- Prove2me | Theorems.Thm_SizeRamsey_Plan_small_graph_data
-- name    : SizeRamsey.Plan.small_graph_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:19.351245+00:00
-- url     : https://prove2.me/theorems/0ee4a677-5694-4442-bedd-63a30fa9dfe5
-- title:
--   Plan: small graph data
-- statement:
--   The Plan construction uses the small graph data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L124-L135
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L124-L135

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.small_graph_data :
    (edgeCount (SimpleGraph.cycleGraph 4) = 4 ∧
      tau4 (SimpleGraph.cycleGraph 4) = 1 ∧
      PrescribedOptimal (SimpleGraph.cycleGraph 4)) ∧
    (edgeCount wheel5 = 8 ∧ tau4 wheel5 = 2 ∧
      PrescribedOptimal wheel5) ∧
    (edgeCount k33MinusEdge = 8 ∧ tau4 k33MinusEdge = 2 ∧
      PrescribedOptimal k33MinusEdge) ∧
    (edgeCount octahedron = 12 ∧ tau4 octahedron = 3 ∧
      PrescribedOptimal octahedron) := by sorry
