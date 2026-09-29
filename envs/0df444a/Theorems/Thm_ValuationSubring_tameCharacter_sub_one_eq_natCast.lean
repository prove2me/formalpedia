-- Prove2me | Theorems.Thm_ValuationSubring_tameCharacter_sub_one_eq_natCast
-- name    : ValuationSubring.tameCharacter_sub_one_eq_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/c8246abb-f094-5a02-b5d3-17c0b0af0d3b
-- title:
--   Tame character of ζ-1 equals the cyclotomic exponent
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$), and let $\zeta \in \overline{\mathbb{Q}}$ lie in $P$, with the residue of $\zeta$ in the residue field $P/\mathfrak{m}_P$ equal to $1$ and with $\zeta \neq 1$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ and $a$ a natural number such that $\sigma \zeta = \zeta^{a}$. Then $P.\mathrm{tameCharacter}$ evaluated at the element $\zeta - 1$ and at $\sigma$ equals the image of $a$ in the residue field of $P$. Here [`ValuationSubring.tameCharacter P π σ`](def/GaloisRep_TameCharacter.html#L7) is defined, for an element $\pi$ of $\overline{\mathbb{Q}}$ and an automorphism $\sigma$, as the residue class of $\sigma\pi/\pi$ when this quotient lies in $P$, and as $0$ otherwise; so the assertion includes the fact that $\sigma(\zeta-1)/(\zeta-1)$ does lie in $P$. No hypothesis places $\sigma$ in an inertia subgroup, and $\zeta$ is not required to be a root of unity; for $a = 0$ both sides are $0$.
--
--   This is the cyclotomic computation identifying the tame character attached to the uniformiser $\zeta - 1$ with the exponent $a$ in $\sigma\zeta = \zeta^{a}$. It is used in this library's study of tame characters and inertia, in particular in the statements about automorphisms with trivial tame character fixing roots of unity, about powers of $\zeta$ and elements of inertia, and in the construction of inertia eigenvectors for the $p$-adic Galois representation of a cusp form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_tameCharacter_sub_one_eq_natCast.lean

import Definitions.Def_GaloisRep_TameCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.tameCharacter_sub_one_eq_natCast
    (P : ValuationSubring (AlgebraicClosure ℚ)) {ζ : AlgebraicClosure ℚ} (hζP : ζ ∈ P)
    (hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1) (hζ1 : ζ ≠ 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {a : ℕ} (hσζ : σ ζ = ζ ^ a) :
    P.tameCharacter (ζ - 1) σ = a := by sorry
