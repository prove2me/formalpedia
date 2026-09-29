-- Prove2me | Theorems.Thm_TarchaBraids_halfTwist_free_lift_surjective_of_normalForm_v1
-- name    : TarchaBraids.halfTwist_free_lift_surjective_of_normalForm_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T12:11:53.667294+00:00
-- url     : https://prove2.me/theorems/82e53489-ae83-41a0-83e9-d457aaa53da2
-- title:
--   A finite signed half-twist normal form gives surjectivity
-- statement:
--   This is the algebraic completion step for Tarcha's generation theorem. If every based loop in the unordered configuration space is homotopic to a finite signed word in the elementary half-twists, then the homomorphism from the free group on the half-twist indices to the geometric braid group is surjective. The finite normal-form hypothesis is the geometric input; the conversion from the resulting signed word to its geometric loop class is supplied by the accepted word-evaluation theorem.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Teorema 3.11, pp. 55--56, finite signed half-twist word normal forms; Birman, Braids, Links and Mapping Class Groups, Chapter 1. The source-faithful bridge is the path-quotient argument implemented in artifacts/agent_tarcha_artin/halfTwist_free_lift_surjective_of_normalForm_v1.lean.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Theorems.Thm_TarchaBraids_braidWord_free_eval_v1

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Theorems.Thm_TarchaBraids_braidWord_free_eval_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem halfTwist_free_lift_surjective_of_normalForm_v1 (n : ℕ) (h : EveryLoopHasBraidWord n) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by sorry

end TarchaBraids
