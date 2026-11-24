-- Prove2me | Theorems.Thm_ValueEquivalence_ve_space_pinned_by_spanning_sets
-- name    : ValueEquivalence.ve_space_pinned_by_spanning_sets
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:51:15.037674+00:00
-- url     : https://prove2.me/theorems/f82e0564-9ee9-45c3-ac4d-dbc5adb4e34c
-- title:
--   Remark 1 (as proved): spanning policies and functions pin down the true model
-- statement:
--   Let $S,A$ be finite, $0<\gamma<1$, $m^*=(r^*,p^*)$ the true model, and $\mathcal M$ a set of models that all have the true reward $r^*$. Let $\Pi\subseteq\boldsymbol\Pi$ and $\mathcal V$ be sets of policies and functions with
--
--   $$\boldsymbol\Pi\subseteq p\text{-span}(\Pi)\qquad\text{and}\qquad\operatorname{span}(\mathcal V)=\mathbb V.$$
--
--   Then $\mathcal M(\Pi,\mathcal V)=\{m^*\}$ or $\mathcal M(\Pi,\mathcal V)=\emptyset$.
--
--   **Formalization Note** The paper states the remark without the two added hypotheses. Both are needed. For $\gamma=0$ any model with the true reward is value equivalent to $m^*$. With learned rewards and $\gamma>0$ there are counterexamples: for one action, two states, $\mathcal V=\{(2,1),(1,0)\}$ (a basis whose coefficients for the constant function sum to $0$), and $\tilde p=p^*+\Delta$ with $\Delta$ having zero row sums, the model $(r^*-\gamma\Delta(1,0)^\top,\tilde p)$ is value equivalent to $m^*$ on $\mathcal V$ but differs from it.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Section 3.2, Remark 1, p. 4

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem ve_space_pinned_by_spanning_sets {S A : Type*} [Fintype S] [Fintype A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (hM : ∀ m ∈ M, m.r = mstar.r)
    (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (hPol : Pol ⊆ policies)
    (hcover : policies ⊆ pspan Pol) (hV : Submodule.span ℝ V = ⊤) :
    veSpace γ M mstar Pol V = {mstar} ∨ veSpace γ M mstar Pol V = ∅ := by sorry

end ValueEquivalence
