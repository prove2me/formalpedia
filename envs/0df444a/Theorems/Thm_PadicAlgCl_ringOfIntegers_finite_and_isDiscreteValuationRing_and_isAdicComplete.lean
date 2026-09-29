-- Prove2me | Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
-- name    : PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/957ac53c-54c7-575b-baee-d29e08909db5
-- title:
--   Ring of integers of a finite extension of ℚₚ
-- statement:
--   Let $p$ be a natural number carrying the hypothesis that it is prime, let $\overline{\mathbb{Q}}_p$ be the algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$, and let $K$ be an intermediate field of the extension $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$ which is assumed finite-dimensional over $\mathbb{Q}_p$. Write $\mathcal{O}_K$ for [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the $\mathbb{Z}_p$-subalgebra of $\overline{\mathbb{Q}}_p$ obtained as the intersection of the integral closure of $\mathbb{Z}_p$ in $\overline{\mathbb{Q}}_p$ with the subalgebra $K$ viewed over $\mathbb{Z}_p$; that is, the set of elements of $K$ that are integral over $\mathbb{Z}_p$. The theorem asserts two things: first, that $\mathcal{O}_K$ is a finite (equivalently, finitely generated) $\mathbb{Z}_p$-module; and second, that there exists a discrete valuation ring structure on $\mathcal{O}_K$ — i.e. $\mathcal{O}_K$ is a local principal ideal domain which is not a field — with respect to which $\mathcal{O}_K$ is adically complete (Hausdorff and precomplete) for the adic filtration by the powers of its maximal ideal. The existential packaging is needed because the statement of adic completeness for the maximal ideal presupposes the local ring structure supplied by the discrete valuation ring instance.
--
--   This is the classical structure theorem for the valuation ring of a $p$-adic field, realised concretely inside a fixed algebraic closure of $\mathbb{Q}_p$: $\mathcal{O}_K$ is a complete discrete valuation ring, finite over $\mathbb{Z}_p$. It supplies the coefficient rings used throughout the $p$-adic Hodge-theoretic and $p$-divisible group arguments, for instance in the Cartier duality and Tate module results that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete.lean

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    Module.Finite ℤ_[p] (PadicAlgCl.ringOfIntegers p K) ∧
    ∃ _ : IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K),
      IsAdicComplete (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K))
        (PadicAlgCl.ringOfIntegers p K) := by sorry
