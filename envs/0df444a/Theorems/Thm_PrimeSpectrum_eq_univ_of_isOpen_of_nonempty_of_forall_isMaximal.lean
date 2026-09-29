-- Prove2me | Theorems.Thm_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
-- name    : PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d37aa1a2-5736-5e95-8fc5-0497e22296fa
-- title:
--   Open, nonempty, maximal-homogeneous subsets of a Jacobson spectrum
-- statement:
--   Let $A$ be a commutative ring which is a Jacobson ring (every radical ideal is an intersection of maximal ideals), and let $U$ be a subset of the prime spectrum $\operatorname{Spec} A$, viewed with its Zariski topology. Assume three things: $U$ is open; $U$ is nonempty; and $U$ is homogeneous on closed points in the strong sense that for all primes $P, Q \in \operatorname{Spec} A$ whose underlying ideals are maximal, membership $P \in U$ already forces $Q \in U$ — that is, if some maximal ideal lies in $U$ then every maximal ideal does. The conclusion is that $U$ is the whole space, $U = \operatorname{Spec} A$ (literally `Set.univ`). Note that the homogeneity hypothesis is stated as a two-point implication quantified over all pairs of maximal ideals, which is the form in which it is consumed, rather than as a statement about a single orbit.
--
--   This is the standard density argument underlying the fact that a nonempty open subscheme of an affine scheme over a Jacobson ring which is homogeneous on closed points exhausts the scheme; the Jacobson hypothesis cannot be dropped (in a discrete valuation ring the generic point is a nonempty open set omitting the closed point). It is used in the Hopf-algebraic part of the development, in the proofs of [`HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed`](thm.html#HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed) and [`HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed`](thm.html#HopfAlgebra.faithfullyFlat_subalgebra_of_isReduced_of_fg_of_isAlgClosed), where a translation-stable nonempty open locus must be shown to be everything.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by sorry
