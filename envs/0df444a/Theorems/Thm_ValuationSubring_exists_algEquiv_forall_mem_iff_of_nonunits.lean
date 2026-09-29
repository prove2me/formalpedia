-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits
-- name    : ValuationSubring.exists_algEquiv_forall_mem_iff_of_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/6b03a175-b119-590e-8a80-aa8b97ae5ae7
-- title:
--   Conjugacy of valuation rings of ℚ̄ with the same residue prime
-- statement:
--   Let $K$ be an intermediate field of $\mathbb Q \subseteq \overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$) which is finite-dimensional over $\mathbb Q$, and let $A$ and $A''$ be valuation subrings of $\overline{\mathbb Q}$. Assume that $A$ and $A''$ agree over $K$ in the weak sense that every $x \in K$ lying in $A$ lies in $A''$, and that for some prime number $q$ the image of $q$ in $\overline{\mathbb Q}$ is a non-unit of both $A$ and $A''$, that is, lies in the maximal ideal of each (equivalently, has valuation $< 1$ for each). Let $L$ be an intermediate field of $K \subseteq \overline{\mathbb Q}$ which is finite-dimensional over $K$. Then there exists a $K$-algebra automorphism $\tau$ of $\overline{\mathbb Q}$, i.e. an element of $\operatorname{Gal}(\overline{\mathbb Q}/K)$, such that for every $x \in L$ one has $x \in A''$ if and only if $\tau x \in A$. Thus $\tau$ carries the restriction of $A$ to $L$ back to the restriction of $A''$ to $L$; no compatibility is asserted outside $L$.
--
--   This is the conjugacy of the prolongations of a valuation of a number field to a finite extension, in the form needed for valuation subrings of $\overline{\mathbb Q}$: two such subrings whose restrictions to $K$ are comparable and whose residue characteristic is the same prime $q$ become equal on any given finite extension $L/K$ after applying a suitable element of $\operatorname{Gal}(\overline{\mathbb Q}/K)$. It is used in the local study of places of modular curves, in the construction of ring homomorphisms with prescribed kernel at a node and in the simultaneous prolongation of places along a tuple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_algEquiv_forall_mem_iff_of_nonunits
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A A'' : ValuationSubring (AlgebraicClosure ℚ))
    (hle : ∀ x : AlgebraicClosure ℚ, x ∈ K → x ∈ A → x ∈ A'')
    {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (hqA'' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A''.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ,
      ∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A'' ↔ τ x ∈ A) := by sorry
