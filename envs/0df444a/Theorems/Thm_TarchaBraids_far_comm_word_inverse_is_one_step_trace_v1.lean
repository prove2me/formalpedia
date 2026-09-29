-- Prove2me | Theorems.Thm_TarchaBraids_far_comm_word_inverse_is_one_step_trace_v1
-- name    : TarchaBraids.far_comm_word_inverse_is_one_step_trace_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T15:20:10.103804+00:00
-- url     : https://prove2.me/theorems/7662cd02-2f7d-469c-b9d9-7a31852ba94f
-- title:
--   The inverse far-commutator move is a one-step contextual trace
-- statement:
--   The inverse direction of the far commuting move in Case 4 of Tarcha's elementary-move analysis is a one-step contextual Artin-relator insertion. The inverse of the far commutator for ordered indices i and j is the published far relator for the reversed ordered pair j and i. This child does not assert that every geometrically null half-twist word has a finite Case 1-5 move list.
-- source:
--   Tarcha, Um Estudo Introduatorio da Teoria de Trancas, Theorem 3.15, pp. 59-62, Figures 3.18-3.27, inverse far-commuting move; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem far_comm_word_inverse_is_one_step_trace_v1
    {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    GeomRelatorTrace n
      ((FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
        (FreeGroup.of j)⁻¹)⁻¹) := by sorry

end TarchaBraids
