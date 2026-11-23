-- Prove2me | Theorems.Thm_ValueEquivalence_ve_space_eq_span
-- name    : ValueEquivalence.ve_space_eq_span
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:50:37.383884+00:00
-- url     : https://prove2.me/theorems/a9ac8e1f-2577-4c37-9fa0-611b51eb80b2
-- title:
--   Proposition 1 (as proved): value equivalence extends to the pointwise span of the policies and the span of the functions
-- statement:
--   Let $S,A$ be finite, $0\le\gamma<1$, $m^*=(r^*,p^*)$ the true model, and $\mathcal M$ a set of models that all have the true reward $r^*$. Let $\Pi\subseteq\boldsymbol\Pi$ be a finite set of policies and $\mathcal V$ a finite set of functions $S\to\mathbb R$. Then
--
--   $$\mathcal M(\Pi,\mathcal V)=\mathcal M\big(p\text{-span}(\Pi)\cap\boldsymbol\Pi,\ \operatorname{span}(\mathcal V)\big).$$
--
--   So value equivalence with respect to $\Pi$ and $\mathcal V$ already gives value equivalence with respect to every policy that is, state by state, a linear combination of policies in $\Pi$, and every linear combination of functions in $\mathcal V$.
--
--   **Formalization Note** The paper states this for models with arbitrary rewards. That version is false: for $\gamma>0$, with two states, one action, $p^*=I$, $r^*=(1,-1)$, $\mathcal V=\{(1,-1)\}$ and $\tilde m=((1+2\gamma)(1,-1),\text{swap})$, the two models agree on $(1,-1)$ but not on $0\in\operatorname{span}(\mathcal V)$. The proof's step $\tilde T_\pi[\sum_i\beta_iv_i]=\sum_i\beta_i\tilde T_\pi[v_i]$ treats the Bellman operator as linear although it is affine. It also fails for $\gamma=0$ when $\mathcal V=\emptyset$: then $\mathcal M(\Pi,\emptyset)=\mathcal M$, while $\operatorname{span}(\emptyset)=\{0\}$ forces $\tilde r_\pi=r^*_\pi$. The statement adds the hypothesis that all models in $\mathcal M$ have the true reward. This is a repair, not an assumption of the paper for this result: the paper introduces "$r$ is known" only later in Section 3.2, for the analysis of Proposition 2. "Discrete" sets are read as finite sets, matching the index range $i\in\{1,\dots,|\mathcal H|\}$ in eq. (3).
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 3.2, Proposition 1, eq. (3), p. 4; proof in Appendix A.1.1, p. 14

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem ve_space_eq_span {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (hM : ∀ m ∈ M, m.r = mstar.r)
    (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (hPolfin : Pol.Finite) (hVfin : V.Finite)
    (hPol : Pol ⊆ policies) :
    veSpace γ M mstar Pol V =
      veSpace γ M mstar (pspan Pol ∩ policies) (Submodule.span ℝ V : Set (S → ℝ)) := by sorry

end ValueEquivalence
