-- Prove2me | Theorems.Thm_ValuationSubring_algHom_apply_mem_of_moduleFinite
-- name    : ValuationSubring.algHom_apply_mem_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/a0c9ccc7-b515-50d8-9f11-05ddc43a697a
-- title:
--   Points of a module-finite algebra lie in a valuation subring
-- statement:
--   Let $R$ be a commutative ring, $L$ a field and $R \to L$ an algebra structure, and let $A$ be a valuation subring of $L$. Assume that the image of $R$ in $L$ is contained in $A$, i.e. $\operatorname{algebraMap}_{R,L}(r) \in A$ for every $r \in R$. Let $H$ be a commutative $R$-algebra which is finite as an $R$-module, and let $f : H \to L$ be a homomorphism of $R$-algebras. Then for every $h \in H$ the element $f(h)$ lies in $A$. Equivalently: an $L$-point of $\operatorname{Spec} H$, for $H$ module-finite over $R$, automatically factors through $A$ whenever $R$ maps into $A$.
--
--   This is the standard fact that a valuation ring, being integrally closed in its fraction field, absorbs all elements integral over a subring it contains; here it is packaged for points of module-finite algebras. It is used in the Raynaud-prolongation arguments for Néron models of modular curves, where $L$ is an algebraic closure of $\mathbb{Q}$, $A$ a valuation subring attached to a place above $p$, $R$ a localisation of $\mathbb{Z}$, and $H$ a finite flat (Hopf) algebra; three results on $p$-divisible groups and Néron objects at $p$ invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_algHom_apply_mem_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.algHom_apply_mem_of_moduleFinite
    {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    (A : ValuationSubring L) (hR : ∀ r : R, algebraMap R L r ∈ A)
    {H : Type} [CommRing H] [Algebra R H] [Module.Finite R H]
    (f : H →ₐ[R] L) (h : H) : f h ∈ A := by sorry
