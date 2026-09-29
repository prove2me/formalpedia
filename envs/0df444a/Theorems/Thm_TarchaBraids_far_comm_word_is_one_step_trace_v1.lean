-- Prove2me | Theorems.Thm_TarchaBraids_far_comm_word_is_one_step_trace_v1
-- name    : TarchaBraids.far_comm_word_is_one_step_trace_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T09:23:11.932992+00:00
-- url     : https://prove2.me/theorems/cb25a418-b311-4bde-8b19-b4e77662657a
-- title:
--   A far commuting Artin relator is one contextual trace step
-- statement:
--   The far-commutator word is one contextual insertion of an Artin commuting relator. This is the algebraic certificate for Case 4 of Tarcha's elementary-move analysis: when two generator indices are at least two apart, the corresponding geometric move is represented by inserting the commuting relator and its inverse. The theorem is independent of the still-open finite completeness theorem that classifies every null geometric word by a sequence of such moves.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem far_comm_word_is_one_step_trace_v1 {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    GeomRelatorTrace n
      (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹) := by sorry

end TarchaBraids
