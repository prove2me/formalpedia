-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top
-- name    : ValuationSubring.isDiscreteValuationRing_inf_toSubring_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b07c8811-dc84-5b89-be94-be9ef6f820c8
-- title:
--   Proper valuation subring of ℚ̄ meets a number field in a DVR
-- statement:
--   Let $O$ be a valuation subring of an algebraic closure $\bar{\mathbb{Q}}$ of $\mathbb{Q}$, assumed not to be the whole field, and let $K$ be an intermediate field of $\bar{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$. The conclusion is a conjunction. First, the subring $O \cap K$ of $\bar{\mathbb{Q}}$, formed as the intersection of the underlying subrings of $O$ and of $K$, is a discrete valuation ring. Second, every element $x$ of $\bar{\mathbb{Q}}$ lying in $K$ can be written as a quotient of elements of that intersection: there exist $a, b \in \bar{\mathbb{Q}}$, both belonging to $O \cap K$, with $b \neq 0$ and $x b = a$. The second clause is phrased element-wise inside $\bar{\mathbb{Q}}$ rather than as an `IsFractionRing` assertion, so it records that $K$ is the fraction field of $O \cap K$ without fixing any algebra structure on the intersection.
--
--   This is the standard statement that a non-trivial valuation of $\bar{\mathbb{Q}}$ restricts to a discrete valuation on each number field, the restricted valuation ring being the localisation of the ring of integers at a prime. It feeds the construction of homomorphism extensions over valuation subrings used in the Cerednik–Drinfeld part of the development, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_inf_toSubring_of_ne_top
    (O : ValuationSubring (AlgebraicClosure ℚ)) (hO : O ≠ ⊤)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    IsDiscreteValuationRing ↥(O.toSubring ⊓ K.toSubring) ∧
      ∀ x : AlgebraicClosure ℚ, x ∈ K →
        ∃ a b : AlgebraicClosure ℚ, a ∈ O.toSubring ⊓ K.toSubring ∧ b ∈ O.toSubring ⊓ K.toSubring ∧
          b ≠ 0 ∧ x * b = a := by sorry
