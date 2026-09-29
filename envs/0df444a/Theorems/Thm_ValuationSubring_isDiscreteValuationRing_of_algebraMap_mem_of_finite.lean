-- Prove2me | Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
-- name    : ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a1914e2a-4c39-5b8c-af44-cdcbeb60ab11
-- title:
--   Krull–Akizuki: valuation subrings over one-dimensional Noetherian domains
-- statement:
--   Let $A$ be a commutative ring which is a Noetherian domain of Krull dimension at most one, let $K$ be a field that is a fraction field of $A$, and let $L$ be a field equipped with $A$- and $K$-algebra structures forming a scalar tower over $A$, with $L$ finite-dimensional as a $K$-vector space (no separability is assumed). Let $\mathcal{O}$ be a valuation subring of $L$, that is, a subring such that for every $x \in L$ either $x \in \mathcal{O}$ or $x^{-1} \in \mathcal{O}$. Assume that the image of every element of $A$ under the structure map $A \to L$ lies in $\mathcal{O}$, and that $\mathcal{O}$ is not the whole of $L$. Then $\mathcal{O}$, regarded as a ring in its own right, is a discrete valuation ring.
--
--   This is the standard corollary of the Krull–Akizuki theorem: a valuation ring, other than the ambient field, of a finite extension of the fraction field of a one-dimensional Noetherian domain and containing that domain is discrete. It is used in the descent of models of curves over a valued algebraically closed field to finite levels, where one intersects the valuation ring of the large field with a finite subextension $L$ of $K$, inseparable extensions included.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by sorry
