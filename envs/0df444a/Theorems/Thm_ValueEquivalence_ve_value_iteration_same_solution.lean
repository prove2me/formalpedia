-- Prove2me | Theorems.Thm_ValueEquivalence_ve_value_iteration_same_solution
-- name    : ValueEquivalence.ve_value_iteration_same_solution
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:53:57.060805+00:00
-- url     : https://prove2.me/theorems/225fc96b-cb99-462c-b830-16bfc35c10df
-- title:
--   Proposition 4 (as proved): value-equivalent models give the same value-iteration solution
-- statement:
--   Let $S,A$ be finite with $A\ne\emptyset$, $0\le\gamma<1$, $m^*=(r^*,p^*)$ the true model with Bellman operators $T_\pi$ and greedy operator $Tv=\max_aT_av$, and $\mathcal M$ a set of models that all have the true reward $r^*$. Let $\Pi\subseteq\boldsymbol\Pi$ and $\mathcal V$ be sets of policies and functions, and let $\mathcal V'$ be a subspace of $\mathbb R^S$ such that
--
--   1. $v\in\mathcal V'$ implies $T_\pi v\in\mathcal V'$ for every policy $\pi\in\boldsymbol\Pi$,
--   2. $p\text{-span}(\Pi)\supseteq\boldsymbol\Pi$, and
--   3. $\operatorname{span}(\mathcal V)=\mathcal V'$.
--
--   Then for every $\tilde m\in\mathcal M(\Pi,\mathcal V)$, with greedy operator $\tilde T$, and every $v'\in\mathcal V'$,
--
--   $$\tilde T^{(n)}v'=T^{(n)}v'\quad\text{for all }n\ge0,$$
--
--   and $\tilde T$ and $T$ have the same fixed points. In particular the optimal value functions agree, $\tilde v^*=v^*$: value iteration with $\tilde m$ started anywhere in $\mathcal V'$ yields the same solution as with $m^*$.
--
--   **Formalization Note** The paper states this for models with arbitrary rewards; that version is false. With two states, one action, $\gamma=1/2$, $p^*=I$, $r^*=(1,-1)$, $\mathcal V=\{(1,-1)\}$ and $\tilde m=(2\cdot(1,-1),\text{swap})$, all hypotheses hold but $v^*=(2,-2)$ and $\tilde v^*=(4/3,-4/3)$. The proof applies Proposition 1, whose span part needs a common reward. The statement therefore adds that all models in $\mathcal M$ have the true reward. "The same solution" is formalized by the equality of all value-iteration iterates from $v'$ and of the fixed points of the greedy operators. Each greedy operator has exactly one fixed point (its optimal value function) because $\gamma<1$.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 4.1, Proposition 4, p. 6; proof in Appendix A.1.1, p. 16

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem ve_value_iteration_same_solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (hM : ∀ m ∈ M, m.r = mstar.r)
    (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (V' : Submodule ℝ (S → ℝ))
    (hPol : Pol ⊆ policies)
    (hclosed : ∀ π ∈ (policies : Set (S → A → ℝ)), ∀ v ∈ V', bellman mstar γ π v ∈ V')
    (hcover : policies ⊆ pspan Pol) (hspan : Submodule.span ℝ V = V')
    (mt : Model S A) (hmt : mt ∈ veSpace γ M mstar Pol V) (v' : S → ℝ) (hv' : v' ∈ V') :
    (∀ n : ℕ, (bellmanOpt mt γ)^[n] v' = (bellmanOpt mstar γ)^[n] v') ∧
    (∀ u : S → ℝ, Function.IsFixedPt (bellmanOpt mt γ) u ↔
      Function.IsFixedPt (bellmanOpt mstar γ) u) := by sorry

end ValueEquivalence
