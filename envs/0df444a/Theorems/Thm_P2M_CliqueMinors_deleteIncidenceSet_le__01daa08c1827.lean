-- Prove2me | Theorems.Thm_P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827
-- name    : P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:46.005404+00:00
-- url     : https://prove2.me/theorems/bf19df8b-833d-55d0-9120-93113127071d
-- title:
--   P2 M Clique Minors delete Incidence Set le  01daa08c1827: P2 M Clique Minors delete Incidence Set le  01daa08c1827
-- statement:
--   The P2 M Clique Minors delete Incidence Set le  01daa08c1827 construction uses the P2 M Clique Minors delete Incidence Set le  01daa08c1827 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L252-L253
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L252-L253

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]

theorem P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827 (G : SimpleGraph V) (v : V) : G.deleteIncidenceSet v ≤ G := by sorry

alias «CliqueMinors».«deleteIncidenceSet_le'» := P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827
