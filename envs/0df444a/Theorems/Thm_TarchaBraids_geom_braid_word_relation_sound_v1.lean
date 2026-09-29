-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_word_relation_sound_v1
-- name    : TarchaBraids.geom_braid_word_relation_sound_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T22:53:45.915309+00:00
-- url     : https://prove2.me/theorems/b6c6121e-83f3-4987-a724-2d5432bc01f6
-- title:
--   A null geometric half-twist word is trivial in the Artin presentation
-- statement:
--   If a finite signed word in elementary geometric half-twists is null-homotopic as a loop of unordered configurations, the corresponding word is the identity in the abstract Artin braid group. Equivalently, every relation among the geometric half-twists follows from Artin's commuting and adjacent braid relations. This isolates the elementary braid-diagram-move analysis in Tarcha's proof of Theorem 3.15, independently of the separate generation theorem.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Theorem 3.15, pp. 59-62, Figures 3.18-3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem geom_braid_word_relation_sound_v1 (n : ℕ)
    (w : FreeGroup (Fin (n - 1)))
    (hw : FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w = 1) :
    PresentedGroup.mk (braidRels n) w = 1 := by sorry

end TarchaBraids
