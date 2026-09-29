-- Prove2me | Theorems.Thm_TarchaBraids_halfTwist_free_lift_surjective_acyclic_v1
-- name    : TarchaBraids.halfTwist_free_lift_surjective_acyclic_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T06:53:24.381694+00:00
-- url     : https://prove2.me/theorems/ba75baa2-dc32-4461-b732-7ce76c5813b0
-- title:
--   Half-twists freely generate the geometric braid group
-- statement:
--   Every geometric braid is represented by a finite word in the elementary half-twists and their inverses. Equivalently, the homomorphism from the free group on the Artin generator indices to the geometric braid group, sending each free generator to its explicit half-twist class, is surjective. This is the generation input from Tarcha's Theorem 3.11, isolated as an acyclic prerequisite for constructing the geometric-to-Artin word homomorphism.
-- source:
--   Tarcha, Um Estudo Introdutorio da Teoria de Trancas, Teorema 3.11, pp. 55-56: partition a geometric braid into finitely many one-crossing slabs, each equivalent to an Artin generator or its inverse; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem halfTwist_free_lift_surjective_acyclic_v1 (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by sorry

end TarchaBraids
