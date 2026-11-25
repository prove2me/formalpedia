-- Prove2me | Theorems.Thm_PerfectGraphTheorem_isPerfect_compl_iff
-- name    : PerfectGraphTheorem.isPerfect_compl_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:01:16.216422+00:00
-- url     : https://prove2.me/theorems/36bd2482-cee8-5dfb-ba59-864c67b64f57
-- title:
--   Perfect Graph Theorem: is Perfect compl iff
-- statement:
--   **The perfect graph theorem (Lovász 1972).** A finite graph is perfect if and only if its
--   complement is perfect.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/Solution.lean#L44-L45
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/Solution.lean#L44-L45

module
public import Mathlib
public import Definitions.Def_PerfectLib_Perfect
public import Definitions.Def_PerfectGraphs_Solution
public import Theorems.Thm_PerfectGraph_isPerfect_compl_iff

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraphTheorem
variable {V : Type*}

theorem PerfectGraphTheorem.isPerfect_compl_iff [Finite V] (G : SimpleGraph V) : IsPerfect Gᶜ ↔ IsPerfect G := by sorry
