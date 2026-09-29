-- Prove2me | Theorems.Thm_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn
-- name    : ValuationSubring.tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/71573c85-8cf5-56eb-9529-37d406c81332
-- title:
--   Independence of the tame character from the chosen root of q
-- statement:
--   Let $q$ be a prime and let $P$ be a valuation subring of $\overline{\mathbb Q}$ (the Lean `AlgebraicClosure ℚ`) satisfying `P.LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb Q}$ lies in the non-units of $P$. Let $\pi,\pi'\in\overline{\mathbb Q}$ both satisfy $\pi^{q^2-1}=q$ and $\pi'^{\,q^2-1}=q$, so each is a root of $X^{q^2-1}-q$. Let $\tau$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lying in `P.inertiaSubgroupIn ℚ`, that is, $\tau$ is the image under the inclusion of the decomposition subgroup of $P$ of an element of the inertia subgroup of $P$. Then the two tame characters agree at $\tau$: `P.tameCharacter π τ = P.tameCharacter π' τ`, where `P.tameCharacter π τ` is by definition the residue in the residue field of $P$ of $\tau\pi/\pi$ when this element lies in $P$, and $0$ otherwise. So the value of the tame character at an inertia element does not depend on which root of $X^{q^2-1}-q$ is used to define it.
--
--   This is the well-definedness of the tame character attached to a place of $\overline{\mathbb Q}$ above $q$, in the form needed to compare two choices of $(q^2-1)$-st root of $q$. It is used in the analysis of the tame inertia action on supersingular charts of modular curves of full level, where a tame-inertia law proved with one explicit root must be transported to the root supplied at rigid level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π π' : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (hπ' : π' ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π τ = P.tameCharacter π' τ := by sorry
