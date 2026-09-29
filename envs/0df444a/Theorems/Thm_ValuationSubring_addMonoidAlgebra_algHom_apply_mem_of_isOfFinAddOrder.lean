-- Prove2me | Theorems.Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
-- name    : ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/d34b3dc8-2a70-5a9b-ba77-856bb43bcd65
-- title:
--   Characters of a torsion monoid algebra land in the valuation subring
-- statement:
--   Let $L$ be a field and $A$ a valuation subring of $L$, let $G$ be an additive monoid in which every element is of finite additive order (the hypothesis $hG$: for all $g : G$, `IsOfFinAddOrder g`), and let $\chi \colon A[G] \to L$ be a homomorphism of $A$-algebras from the additive monoid algebra of $G$ over $A$ into $L$, where $L$ is viewed as an $A$-algebra via the inclusion of the valuation subring. The conclusion is a conjunction: first, $\chi(x) \in A$ for every $x \in A[G]$; second, there exists an $A$-algebra homomorphism $\chi_A \colon A[G] \to A$ such that the image of $\chi_A(x)$ under the inclusion $A \hookrightarrow L$ equals $\chi(x)$ for every $x$. Thus $\chi$ factors, as an $A$-algebra map, through the valuation subring, and the factorisation is exhibited rather than merely asserted to exist abstractly. No finiteness or commutativity assumption on $G$ beyond the torsion hypothesis is imposed, and the valuation is arbitrary (no rank or discreteness condition).
--
--   This is the statement that the $L$-valued characters of a torsion monoid algebra over a valuation ring are automatically $A$-valued, the algebraic form of the assertion that the $L$-points of a diagonalisable group scheme $\operatorname{Spec} A[G]$ with $G$ torsion are already $A$-points. It is used in the analysis of the toric part of the Néron model of a Jacobian at a prime of bad reduction, in particular for the character lattice and the filtration on the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AddMonoidAlgebra

theorem ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
    {L : Type u} [Field L] (A : ValuationSubring L)
    {G : Type v} [AddMonoid G] (hG : ∀ g : G, IsOfFinAddOrder g)
    (χ : AddMonoidAlgebra A G →ₐ[A] L) :
    (∀ x, χ x ∈ A) ∧ ∃ χA : AddMonoidAlgebra A G →ₐ[A] A, ∀ x, (χA x : L) = χ x := by sorry
