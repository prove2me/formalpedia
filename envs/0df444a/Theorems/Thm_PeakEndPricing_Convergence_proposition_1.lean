-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_proposition_1
-- name    : PeakEndPricing.Convergence.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:15.001506+00:00
-- url     : https://prove2.me/theorems/d872d120-5ebe-430f-ba2f-454720ed595e
-- title:
--   Proposition 1 — the steady states of (7) are {(m, p**_λ(m)) : m ∈ R₁} ∪ {(m, m) : m ∈ R₂}; p**_λ(m) is decreasing in λ and increasing in β
-- statement:
--   Under the standing hypotheses of Section 3, let $s, S\in\mathbf P$ solve (9) and (10), and let $\mathbf R_1 = [0,s]$, $\mathbf R_2 = [s,S]$. Then a pair $(m,p)$ is a steady state of Problem (7) — that is, $m,p\in\mathbf P$, $m\le p$, and the constant path $p_t\equiv p$ is optimal from $(m,p)$ — if and only if
--   $$\big(m\in\mathbf R_1,\ p\in\mathbf P,\ \pi_0'(p) - \lambda(2-(1-\theta)(1+\beta))p + \lambda\theta m = 0\big) \quad\text{or}\quad \big(m\in\mathbf R_2,\ p = m\big).$$
--   In the paper's notation, the set of steady states is $\{(m, p^{**}_\lambda(m)) \mid m\in\mathbf R_1\}\cup\{(m,m)\mid m\in\mathbf R_2\}$.
--
--   Moreover (the proposition's second sentence, "the value of the steady state prices is decreasing in $\lambda$, and increasing in $\beta$"): for every $m\in\mathbf R_1$, the steady-state price $p^{**}_\lambda(m)$ is (weakly) decreasing in $\lambda$ and (weakly) increasing in $\beta$. That is, if $x\in\mathbf P$ solves (12) at $(\lambda,\beta,m)$ and $x'\in\mathbf P$ solves (12) at $(\lambda',\beta,m)$ with $\lambda'\ge\lambda$, then $x'\le x$; and if $x'\in\mathbf P$ solves (12) at $(\lambda,\beta',m)$ with $\beta\le\beta'<1$, then $x\le x'$.
--
--   The proposition identifies the long-run prices: a continuum of steady states, each determined by the remembered minimum price.
--
--   **Formalization Note** $p^{**}_\lambda(m)$ is represented by the condition "$p\in\mathbf P$ solves (12)", which has at most one solution. The paper's "the value of the steady state prices" is read, as in its proof (p. 45: "Finally, $p^{**}_\lambda(m)$ is decreasing in $\lambda$"), as the steady-state price $p^{**}_\lambda(m)$ attached to a fixed $m\in\mathbf R_1$ (for $m\in\mathbf R_2$ the steady-state price is $m$ itself and does not depend on $\lambda,\beta$); the perturbed roots are roots of (12) only, so the other model hypotheses need not be re-stated at $\lambda'$, $\beta'$.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 11, Proposition 1

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem proposition_1 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) :
    (∀ m p : ℝ, IsSteadyState pbar d0 lam gam theta beta m p ↔
      (m ∈ Set.Icc (0 : ℝ) s ∧ p ∈ Set.Icc (0 : ℝ) pbar ∧ eq12 d0 lam theta beta m p) ∨
      (m ∈ Set.Icc s S ∧ p = m)) ∧
    (∀ m ∈ Set.Icc (0 : ℝ) s, ∀ x ∈ Set.Icc (0 : ℝ) pbar, eq12 d0 lam theta beta m x →
      (∀ lam' : ℝ, lam ≤ lam' → ∀ x' ∈ Set.Icc (0 : ℝ) pbar,
        eq12 d0 lam' theta beta m x' → x' ≤ x) ∧
      (∀ beta' : ℝ, beta ≤ beta' → beta' < 1 → ∀ x' ∈ Set.Icc (0 : ℝ) pbar,
        eq12 d0 lam theta beta' m x' → x ≤ x')) := by sorry

end PeakEndPricing.Convergence
