-- Prove2me | Theorems.Thm_Tarcha_halfTwist_free_lift_surjective_acyclic_v1
-- name    : Tarcha.halfTwist_free_lift_surjective_acyclic_v1
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-26T23:36:36.15701+00:00
-- url     : https://prove2.me/theorems/0fd0aa4a-efe1-4694-8005-f76cd887f183
-- title:
--   Surjectivity of the free-group lift for a word-generated group
-- statement:
--   The algebraic half of the Tarcha Theorem 3.11 half-twist generation argument. If every element of a group G is a finite product of elements of the form f(i) or f(i)⁻¹ for a family f : ι → G (each group element realized as a word in the generators and their inverses), then the universal homomorphism FreeGroup.lift f from the free group on ι to G is surjective. This is the pure-algebra input to TarchaBraids.halfTwist_free_lift_surjective_acyclic_v1: the geometric half supplies the word hypothesis (every geometric braid is a word in half-twists and their inverses), and this lemma turns that hypothesis into surjectivity of the lift. Mathlib-native and independent of the mission geometry; mission-connected via the assembly into the Tarcha braids track.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Teorema 3.11, pp. 55-56 (generation by half-twists); algebraic half of the decomposition of TarchaBraids.halfTwist_free_lift_surjective_acyclic_v1.

import Mathlib

set_option autoImplicit false

namespace Tarcha

theorem halfTwist_free_lift_surjective_acyclic_v1 {ι : Type} {G : Type} [Group G]
    (f : ι → G)
    (hgen : ∀ g : G, ∃ l : List (ι × Bool),
      g = (l.map fun p => if p.2 then f p.1 else (f p.1)⁻¹).prod) :
    Function.Surjective (FreeGroup.lift f) := by
  sorry

end Tarcha
