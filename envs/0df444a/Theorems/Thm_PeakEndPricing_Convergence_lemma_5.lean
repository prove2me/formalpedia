-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_lemma_5
-- name    : PeakEndPricing.Convergence.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:42.301987+00:00
-- url     : https://prove2.me/theorems/3db92a4a-6c59-4e1a-993c-511a37642263
-- title:
--   Lemma 5 — (m, p**_λ(m)) is a steady state of (7) for m ∈ R₁, and (m, m) for m ∈ R₂
-- statement:
--   Under the standing hypotheses of Section 3, let $s, S\in\mathbf P$ solve (9) and (10), and let $\mathbf R_1 = [0,s]$, $\mathbf R_2 = [s,S]$. A steady state of Problem (7) is a state $(m,p)$, $m,p\in\mathbf P$, $m\le p$, from which the constant path $p_t\equiv p$ is optimal. Then:
--
--   1. (a) for every $m\in\mathbf R_1$ there is $x\in\mathbf P$ solving
--   $$\pi_0'(x) - \lambda(2-(1-\theta)(1+\beta))x + \lambda\theta m = 0 \qquad (12)$$
--   such that $(m, x)$ is a steady state of Problem (7) — the paper's $(m, p^{**}_\lambda(m))$;
--   2. (b) for every $m\in\mathbf R_2$, $(m,m)$ is a steady state of Problem (7).
--
--   These are the two families of steady states; Proposition 1 shows there are no others.
--
--   **Formalization Note** The paper names the root of (12) $p^{**}_\lambda(m)$; the statement asserts the existence of a root $x \in \mathbf P$ with the property (the root is unique because the left side of (12) is strictly decreasing). Membership $m \le x$ is part of the steady-state definition.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 11, Lemma 5 (with (12))

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem lemma_5 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S) :
    (∀ m ∈ Set.Icc (0 : ℝ) s, ∃ x ∈ Set.Icc (0 : ℝ) pbar,
      eq12 d0 lam theta beta m x ∧ IsSteadyState pbar d0 lam gam theta beta m x) ∧
    (∀ m ∈ Set.Icc s S, IsSteadyState pbar d0 lam gam theta beta m m) := by sorry

end PeakEndPricing.Convergence
