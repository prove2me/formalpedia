-- Prove2me | Theorems.Thm_PCB_lex_cone_trichotomy
-- name    : PCB.lex_cone_trichotomy
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:08:07.992145+00:00
-- url     : https://prove2.me/theorems/ef1826c1-a6cf-4789-8169-2fe481ee7d49
-- title:
--   The lexicographic cone satisfies the trichotomy law (Theorem 4 (ii))
-- statement:
--   The lexicographic cone satisfies the trichotomy law of Definition 1. Every non-identity element has a highest nontrivial component in its normal form; since the Magnus-type cone of the corresponding free factor satisfies the trichotomy law, either the element or its inverse lies in the lexicographic cone, and never both. This is Theorem 4 (ii) of the paper.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Theorem 4 (ii)).

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB

/-!  Milestone 2 (Theorem 4 (ii)): the lexicographic cone satisfies the
trichotomy law. Every non-identity element has a highest nontrivial
component in its normal form; since the Magnus-type cone of the
corresponding free factor satisfies trichotomy, either the element or its
inverse lies in the lexicographic cone, and never both. -/
theorem lex_cone_trichotomy {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    (∀ g : G, g ≠ 1 → (g ∈ lexCone W ∨ g⁻¹ ∈ lexCone W)) ∧
    (∀ g ∈ lexCone W, g⁻¹ ∉ lexCone W) := by sorry

end PCB
