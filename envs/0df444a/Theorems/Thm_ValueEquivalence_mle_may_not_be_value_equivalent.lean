-- Prove2me | Theorems.Thm_ValueEquivalence_mle_may_not_be_value_equivalent
-- name    : ValueEquivalence.mle_may_not_be_value_equivalent
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:53:07.804603+00:00
-- url     : https://prove2.me/theorems/6cea7ab8-b7f7-419a-9825-508c0743d689
-- title:
--   Proposition 3: the maximum-likelihood model may miss a nonempty space of value-equivalent models
-- statement:
--   The maximum-likelihood estimate of $p^*$ in a class $\mathcal P$ of transition kernels may fail to belong to the space $\mathcal P(\Pi,\mathcal V)$ of value-equivalent kernels in $\mathcal P$ even when that space is nonempty. Precisely: there exist finite $S$ and $A$, a discount $0\le\gamma<1$, a true model $m^*=(r^*,p^*)$, a class $\mathcal P$ of transition kernels, a set of policies $\Pi\subseteq\boldsymbol\Pi$, a set of functions $\mathcal V$ and a distribution $D$ on $S\times A$ such that
--
--   1. $\mathcal P(\Pi,\mathcal V)\ne\emptyset$,
--   2. the maximum-likelihood loss $\tilde p\mapsto\ell_{p,D}(p^*,\tilde p)$ of eq. (5) attains its minimum on $\mathcal P$, and
--   3. no minimiser of $\ell_{p,D}(p^*,\cdot)$ over $\mathcal P$ lies in $\mathcal P(\Pi,\mathcal V)$.
--
--   **Formalization Note** "May not belong" is formalized as the existence of such an instance; the finite sets are taken to be $\{0,\dots,n-1\}$, which loses no generality. Every minimiser, not just one, is required to lie outside $\mathcal P(\Pi,\mathcal V)$, so that the statement holds whichever minimiser is called the maximum-likelihood estimate.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 4, Proposition 3, eq. (5), p. 5; proof in Appendix A.1.1, pp. 15-16

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem mle_may_not_be_value_equivalent :
    ∃ (nS nA : ℕ) (γ : ℝ) (mstar : Model (Fin nS) (Fin nA))
      (PP : Set (Fin nS → Fin nA → Fin nS → ℝ)) (Pol : Set (Fin nS → Fin nA → ℝ))
      (V : Set (Fin nS → ℝ)) (D : Fin nS → Fin nA → ℝ),
      0 ≤ γ ∧ γ < 1 ∧ Pol ⊆ policies ∧ (∀ P ∈ PP, IsTransitionKernel P) ∧
      (∀ s a, 0 ≤ D s a) ∧ ∑ s, ∑ a, D s a = 1 ∧
      (veKernels γ mstar PP Pol V).Nonempty ∧
      (∃ P ∈ PP, ∀ P' ∈ PP, mleLoss D mstar.p P ≤ mleLoss D mstar.p P') ∧
      ∀ P ∈ PP, (∀ P' ∈ PP, mleLoss D mstar.p P ≤ mleLoss D mstar.p P') →
        P ∉ veKernels γ mstar PP Pol V := by sorry

end ValueEquivalence
