-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_pi_isPolyhedron_isContractible
-- name    : SocialEquilibrium.Existence.pi_isPolyhedron_isContractible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:41:24.920364+00:00
-- url     : https://prove2.me/theorems/f0701a6c-6049-4358-a9ee-68b3b068ea6d
-- title:
--   Proof of the THEOREM — the product of ν contractible polyhedra is a contractible polyhedron
-- statement:
--   Let $\iota$ range over a finite set of agents, and for each $\iota$ let $\mathfrak A_\iota$ be a contractible polyhedron in a finite-dimensional real normed space $E_\iota$. Then the product
--   $$\mathfrak A=\prod_\iota\mathfrak A_\iota\subseteq\prod_\iota E_\iota$$
--   is a contractible polyhedron.
--
--   This is the finite-product form of the §1 product results, and it is the form the proof of the existence theorem uses: the fixed-point LEMMA is applied on $\mathfrak A$.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, §2 proof of the THEOREM, first paragraph (first sentence)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, first paragraph): the product
`𝔄 = 𝔄_1 × ⋯ × 𝔄_ν` of finitely many contractible polyhedra is a contractible polyhedron. -/
theorem pi_isPolyhedron_isContractible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (hX : ∀ i, IsPolyhedron (X i) ∧ IsContractible (X i)) :
    IsPolyhedron (Set.univ.pi X) ∧ IsContractible (Set.univ.pi X) := by sorry

end SocialEquilibrium.Existence
