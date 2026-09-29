-- Prove2me | Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
-- name    : RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/911f98fb-18b1-531c-8601-6b27f420a624
-- title:
--   Values of a ring map on a module-finite algebra generate a finite extension
-- statement:
--   Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra that is finite as an $R$-module, and let $K$ be a field which is an algebra over a field $E$. Let $\chi' : S \to K$ be a ring homomorphism (not assumed $R$- or $E$-linear) and assume that for every $r \in R$ the element $\chi'(\mathrm{algebraMap}_{R,S}(r))$ lies in the range of the structure map $E \to K$. The conclusion is that the intermediate field $E(\operatorname{range} \chi')$ of $K/E$, that is, the subfield of $K$ generated over (the image of) $E$ by the set of all values of $\chi'$, is finite-dimensional as an $E$-vector space. No finiteness or separability hypothesis on $E$, $K$ or $R$ is imposed, and $\chi'$ is not required to be injective or surjective.
--
--   This is the standard statement that the coefficient field cut out by a character of a module-finite algebra is a finite extension: for instance the field generated over $\mathbb{Q}_p$ (or over the fraction field of a coefficient ring) by the Hecke eigenvalues of an eigenform, the Hecke algebra being finite over $\mathbb{Z}$. It is used in the construction of the $p$-adic Galois representation attached to an eigenform and in the constructions of curves over rings of Krull dimension one that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
    {R S E K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field E] [Field K] [Algebra E K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
    FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) := by sorry
