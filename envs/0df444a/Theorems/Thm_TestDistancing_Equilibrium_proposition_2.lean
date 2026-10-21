-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_proposition_2
-- name    : TestDistancing.Equilibrium.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:02.375684+00:00
-- url     : https://prove2.me/theorems/466fac5f-41f4-4093-a7de-5a2547a9db78
-- title:
--   Proposition 2, corrected — unique symmetric equilibrium in four policy regions (degenerate corner p = 0, α_L = 1 excluded in A_1–A_3)
-- statement:
--   Under the model's standing assumptions there is a positive integer $M$ such that, for every $n\ge M$ and policy $\alpha=(\alpha_L,\alpha_H)$, the unique symmetric equilibrium has the following typewise activity probabilities $\gamma=(\gamma_L,\gamma_H)$:
--
--   $$\alpha\in A_1:\gamma=(1,1);\quad\alpha\in A_2:\gamma=(g_L,1);\quad\alpha\in A_3:\gamma=(0,1);\quad\alpha\in A_4:\gamma=(0,g_H),$$
--
--   where $g_L,g_H\in[0,1]$ depend on policy. The theorem asserts existence and uniqueness in each region. The regions may share boundaries; their descriptions must agree there. In regions $A_1$, $A_2$, $A_3$ the policy is required to satisfy $p=0\Rightarrow\alpha_L<1$.
--
--   **Formalization Note** The page has no such restriction, but without it the proposition is false: if $p=0$ and $\alpha_L=1$, low-value agents never transmit, so the low agent's infection probability does not depend on the other low agents' activity. Choosing $\alpha_H$ with $\mathbb P^{\inf}_l(\mathbf x=\mathbf 1)=v_L+1/n$ (possible for every large $n$ when $v_L$ is small, e.g. $v_L=0.01$, $\eta=\beta=1$, $r_H=1/2$, or with $v_L=0$ and $\alpha=(1,1)$) puts the policy in $A_1\cap A_2\cap A_3$, and every $(g,1)$ with $g\in[0,1]$ is a symmetric equilibrium. Part (d) needs no restriction. Symmetric strategies are typewise mixtures on $\{0,1\}$; high types are the first $\lceil r_H n\rceil$ agents.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 11 (PDF 13), Proposition 2(a)–(d)

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

/-- Proposition 2, with one correction. In parts (a)–(c) the policy must not make low-value
agents certain non-transmitters (`p = 0` together with `α_L = 1`): at such a policy with
`P^inf_l(x = 1) = v_L + 1/n` the policy lies in `A_1 ∩ A_2 ∩ A_3`, every low-type mixing
probability is an equilibrium, and the printed uniqueness fails. -/
theorem proposition_2 (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n →
      (∀ α ∈ A1 P n, (P.p = 0 → α.1 < 1) → ∀ γ : ℝ × ℝ,
        IsSymEq P n γ α ↔ γ = (1, 1)) ∧
      (∀ α ∈ A2 P n, (P.p = 0 → α.1 < 1) → ∃ g : ℝ, g ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ γ : ℝ × ℝ, IsSymEq P n γ α ↔ γ = (g, 1)) ∧
      (∀ α ∈ A3 P n, (P.p = 0 → α.1 < 1) → ∀ γ : ℝ × ℝ,
        IsSymEq P n γ α ↔ γ = (0, 1)) ∧
      (∀ α ∈ A4 P n, ∃ g : ℝ, g ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ γ : ℝ × ℝ, IsSymEq P n γ α ↔ γ = (0, g)) := by sorry

end TestDistancing.Equilibrium
