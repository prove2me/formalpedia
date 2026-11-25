-- Prove2me | Theorems.Thm_PerfectGraph_isPerfect_compl_iff
-- name    : PerfectGraph.isPerfect_compl_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:30:28.628402+00:00
-- url     : https://prove2.me/theorems/16d414bb-9494-51fc-9e48-aa8732445795
-- title:
--   Perfect Graph: is Perfect compl iff
-- statement:
--   **The perfect graph theorem (Lovász 1972).** A finite graph is perfect if and only if its
--   complement is perfect.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Perfect.lean#L62-L65
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Perfect.lean#L62-L65

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Definitions.Def_PerfectLib_Perfect
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraph
variable {V : Type*}

theorem PerfectGraph.isPerfect_compl_iff [Finite V] (G : SimpleGraph V) : IsPerfect Gᶜ ↔ IsPerfect G := by sorry
