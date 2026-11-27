-- Prove2me | Theorems.Thm_SizeRamsey_Plan_octahedronPres_spec
-- name    : SizeRamsey.Plan.octahedronPres_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:16.380795+00:00
-- url     : https://prove2.me/theorems/7fb2d9b0-a29a-58b6-95cc-292bdbe97cd2
-- title:
--   Plan: octahedron Pres spec
-- statement:
--   The Plan construction uses the octahedron Pres spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L60-L62
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L60-L62

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.octahedronPres_spec : ∀ v, v ∈ octahedronPres v ∧ (octahedronPres v).card = 3 ∧
    QTrans octahedron (octahedronPres v) := by sorry
