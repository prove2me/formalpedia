-- Prove2me | Theorems.Thm_SizeRamsey_Plan_octahedron_tau
-- name    : SizeRamsey.Plan.octahedron_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:32.875992+00:00
-- url     : https://prove2.me/theorems/d1fc0151-2fc5-48c1-ad24-f332bafa3ba6
-- title:
--   Plan: octahedron tau
-- statement:
--   The Plan construction uses the octahedron tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L102-L104
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L102-L104

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.octahedron_tau : tau4 octahedron = 3 ∧ PrescribedOptimal octahedron := by sorry
