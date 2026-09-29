-- Prove2me | Theorems.Thm_TarchaBraids_geom_null_word_has_contextual_relator_trace_v1
-- name    : TarchaBraids.geom_null_word_has_contextual_relator_trace_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T07:35:37.539559+00:00
-- url     : https://prove2.me/theorems/0cf542cd-ea28-4f59-a4a7-23440fab6b0e
-- title:
--   A null geometric half-twist word has a finite contextual relator trace
-- statement:
--   This is the genuinely geometric half of Tarcha's Theorem 3.15. Whenever a finite signed word in elementary geometric half-twists is null-homotopic in the unordered configuration space, the elementary braid-diagram move analysis in Figures 3.18--3.27 expresses that word as a finite trace of contextual insertions of Artin commuting and adjacent braid relators. The accepted adjacent and outer-rotation certificates verify the individual move calculations; this child asserts the remaining finite-completeness theorem. It is independent of the algebraic relator-conjugacy child, which is used afterward.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_quotient_eq_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_word_eq_outer_quotient_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_eq_outer_quotient_v1

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_quotient_eq_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_word_eq_outer_quotient_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_eq_outer_quotient_v1

namespace TarchaBraids

open BraidsLinksMCG

/-- Tarcha 3.15, Figures 3.18--3.27: a null geometric half-twist word is
written as finitely many contextual insertions of Artin relators. -/
theorem geom_null_word_has_contextual_relator_trace_v1 (n : ℕ) (w : FreeGroup (Fin (n - 1)))
    (hw : FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w = 1) :
    GeomRelatorTrace n w := by sorry

end TarchaBraids
