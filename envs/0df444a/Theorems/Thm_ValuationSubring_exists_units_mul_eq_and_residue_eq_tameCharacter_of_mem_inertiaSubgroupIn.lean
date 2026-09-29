-- Prove2me | Theorems.Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
-- name    : ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/f685cb34-c747-5ae2-8280-359bae468d1e
-- title:
--   Inertia acts by units with residue the tame character
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in `A.inertiaSubgroupIn ℚ`, that is, in the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$ into the full automorphism group. Here `A.tameCharacter z σ` denotes the element of the residue field of $A$ equal to the residue of $\sigma(z)/z$ when $\sigma(z)/z$ lies in $A$, and $0$ otherwise. The conclusion is a conjunction of two assertions. First, for every $z \in \overline{\mathbb{Q}}$ with $z \neq 0$ there exists a unit $a$ of the ring $A$ such that the image of $a$ in $\overline{\mathbb{Q}}$ satisfies $a \cdot z = \sigma(z)$ and such that the residue of $a$ in the residue field of $A$ equals `A.tameCharacter z σ`. Second, for every unit $u$ of $A$, the value `A.tameCharacter u σ` at the image of $u$ in $\overline{\mathbb{Q}}$ is $1$.
--
--   This is the tame Kummer description of the action of inertia: for $\sigma$ inertial, $\sigma(z)/z$ is a unit of the valuation ring, its residue is by definition the tame character at $z$, and the tame character is insensitive to replacing $z$ by a unit multiple. It is used in the analysis of prolongations of places on modular curves, for instance in [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self) and its annulus variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
      ∃ a : (↥A)ˣ, ((a : ↥A) : AlgebraicClosure ℚ) * z = σ z ∧
        IsLocalRing.residue (↥A) (a : ↥A) = A.tameCharacter z σ) ∧
    ∀ u : (↥A)ˣ, A.tameCharacter ((u : ↥A) : AlgebraicClosure ℚ) σ = 1 := by sorry
