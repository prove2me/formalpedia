-- Prove2me | Theorems.Thm_ValuationSubring_exists_algHom_forall_apply_mem_iff_of_isAlgebraic
-- name    : ValuationSubring.exists_algHom_forall_apply_mem_iff_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/106e69c8-f75e-55ae-ba01-f31d2e92ac06
-- title:
--   Extensions of valuations to algebraic extensions come from embeddings
-- statement:
--   Let $K$ be a field equipped with an algebra structure over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, i.e. with a ring homomorphism $K \to \overline{\mathbb{Q}}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $L$ be a field which is a $K$-algebra and algebraic over $K$, and let $V$ be a valuation subring of $L$. Assume that $V$ and $A$ induce the same valuation subring of $K$, in the sense that for every $x \in K$ the element $\mathrm{algebraMap}\,K\,L\,x$ lies in $V$ if and only if $\mathrm{algebraMap}\,K\,\overline{\mathbb{Q}}\,x$ lies in $A$. Then there exists a $K$-algebra homomorphism $\tau : L \to \overline{\mathbb{Q}}$ such that for all $y \in L$ one has $\tau(y) \in A$ if and only if $y \in V$; that is, $V$ is the pull-back $\tau^{-1}(A)$ of $A$ along a $K$-embedding of $L$ into $\overline{\mathbb{Q}}$. Here $K$ and $L$ are taken in the lowest universe.
--
--   This is the classical statement that the extensions of a valuation of $K$ to an algebraic extension $L$ are exactly the pull-backs of a fixed valuation ring of an algebraic closure along the various $K$-embeddings of $L$ (equivalently, that such extensions are conjugate). It is used to construct, from a valuation subring of a number field or of an algebraic extension, a compatible embedding into $\overline{\mathbb{Q}}$ together with a local ring homomorphism of the associated discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algHom_forall_apply_mem_iff_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_algHom_forall_apply_mem_iff_of_isAlgebraic
    (K : Type) [Field K] [Algebra K (AlgebraicClosure ℚ)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (L : Type) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ algebraMap K (AlgebraicClosure ℚ) x ∈ A) :
    ∃ τ : L →ₐ[K] AlgebraicClosure ℚ, ∀ y : L, τ y ∈ A ↔ y ∈ V := by sorry
