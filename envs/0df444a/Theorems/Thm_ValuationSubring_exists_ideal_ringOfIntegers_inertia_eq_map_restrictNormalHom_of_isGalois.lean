-- Prove2me | Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
-- name    : ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/3c48ea84-832e-57cf-84c0-924a77de4d16
-- title:
--   Inertia of a place of ℚ̄ surjects onto finite layers
-- statement:
--   Let $F$ be a number field equipped with an algebra structure over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $P$ be a valuation subring of $\overline{\mathbb{Q}}$, let $q$ be a prime number, and assume that $P$ lies over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ is a non-unit of $P$. Let $M$ be an intermediate field of $\overline{\mathbb{Q}}/F$ that is finite-dimensional and Galois over $F$. The assertion is that there exists an ideal $Q$ of the ring of integers $\mathcal{O}_M$ of $M$ such that: $Q$ is maximal; every $x \in \mathcal{O}_M$ satisfies $P$-valuation $\le 1$ at its image in $\overline{\mathbb{Q}}$ (that is, $\mathcal{O}_M \subseteq P$); for $x \in \mathcal{O}_M$ one has $x \in Q$ if and only if the $P$-valuation of its image is $< 1$ (so $Q$ is the contraction of the maximal ideal of $P$); and the image of $P$'s inertia subgroup over $F$ — the inertia subgroup of $P$ inside the decomposition subgroup of $P$ over $F$, transported along the inclusion of that decomposition subgroup into $\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[F]} \overline{\mathbb{Q}}$ — under the restriction homomorphism `AlgEquiv.restrictNormalHom` to $M \simeq_{\mathrm{alg}[F]} M$ equals the inertia group of $Q$ for the action of $M \simeq_{\mathrm{alg}[F]} M$ on $\mathcal{O}_M$.
--
--   This is the compatibility of inertia groups in towers from Hilbert's ramification theory: the inertia group at a place of $\overline{\mathbb{Q}}$ above $q$, taken relative to the number field $F$, restricts onto the inertia group of the induced maximal ideal in each finite Galois layer $M/F$, and the statement simultaneously identifies that maximal ideal valuation-theoretically. It is used in the construction of the discrete valuation ring attached to the fixed field of the inertia subgroup, in [`ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible`](thm.html#ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn_of_irreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom_of_isGalois
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M] :
    ∃ Q : Ideal (NumberField.RingOfIntegers ↥M), Q.IsMaximal ∧
      (∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1) ∧
      (∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1) ∧
      (P.inertiaSubgroupIn F).map (AlgEquiv.restrictNormalHom ↥M) = Q.inertia (↥M ≃ₐ[F] ↥M) := by sorry
