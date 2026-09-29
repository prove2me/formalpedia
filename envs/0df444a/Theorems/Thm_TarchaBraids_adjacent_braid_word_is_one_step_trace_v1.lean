-- Prove2me | Theorems.Thm_TarchaBraids_adjacent_braid_word_is_one_step_trace_v1
-- name    : TarchaBraids.adjacent_braid_word_is_one_step_trace_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T08:20:33.625865+00:00
-- url     : https://prove2.me/theorems/e8ca80f6-0d47-47ce-a503-ba1f5a92cf3e
-- title:
--   An adjacent Artin relator is one contextual trace step
-- statement:
--   An adjacent Artin braid relator is a single contextual relator-trace step. This is the algebraic certificate for one adjacent three-crossing move in the finite geometric move analysis used to prove that every null geometric half-twist word is a finite product of Artin relators. It is independent of the finite-trace parent and imports only the published trace and Artin-presentation definitions.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, adjacent braid move; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem adjacent_braid_word_is_one_step_trace_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    GeomRelatorTrace n
      (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) := by sorry

end TarchaBraids
