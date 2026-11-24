-- Prove2me | Theorems.Thm_ValueEquivalence_ve_space_all_policies_all_functions
-- name    : ValueEquivalence.ve_space_all_policies_all_functions
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:49:37.563737+00:00
-- url     : https://prove2.me/theorems/2117be66-0432-42cb-b802-f81e0dd6abed
-- title:
--   Property 2 (as proved): M(𝚷, 𝕍) either contains m* or is empty
-- statement:
--   Let $S,A$ be finite, $0<\gamma<1$, $m^*$ the true model and $\mathcal M$ any set of models. Then the space of models in $\mathcal M$ that are value equivalent to $m^*$ with respect to all policies $\boldsymbol\Pi$ and all functions $\mathbb V$ either contains $m^*$ or is empty:
--
--   $$m^*\in\mathcal M(\boldsymbol\Pi,\mathbb V)\quad\text{or}\quad\mathcal M(\boldsymbol\Pi,\mathbb V)=\emptyset.$$
--
--   **Formalization Note** The paper allows $\gamma\in[0,1)$. For $\gamma=0$ the Bellman operators do not depend on the transition kernel, so a set $\mathcal M=\{\tilde m\}$ with $\tilde m=(r^*,\tilde p)$, $\tilde p\ne p^*$, is a counterexample. The statement therefore assumes $\gamma>0$, which is what the paper's proof uses when it asserts that only $m^*$ induces the true Bellman operators.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 3.1, Property 2, p. 3; proof in Appendix A.1.1, p. 13

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem ve_space_all_policies_all_functions {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A) :
    mstar ∈ veSpace γ M mstar policies Set.univ ∨
      veSpace γ M mstar policies Set.univ = ∅ := by sorry

end ValueEquivalence
