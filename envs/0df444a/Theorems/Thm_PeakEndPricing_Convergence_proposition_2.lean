-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_proposition_2
-- name    : PeakEndPricing.Convergence.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:22.903015+00:00
-- url     : https://prove2.me/theorems/7a041a5c-d96c-423b-952a-ceba2055510a
-- title:
--   Proposition 2 — if m₀ ∈ R₁ ∪ R₂ then p_t ≥ m₀ for all t; if m₀ ∈ R₃ then m_t ∈ R₃ for all t
-- statement:
--   Under the standing hypotheses of Section 3, let $s,S\in\mathbf P$ solve (9) and (10), and $\mathbf R_1 = [0,s]$, $\mathbf R_2 = [s,S]$, $\mathbf R_3 = [S,\bar p]$. Let $(m_0,p_0)$ be an initial state with $m_0,p_0\in\mathbf P$, $m_0\le p_0$, and let $\{p_t\}_{t\ge1}$ be an optimal price path from it, with minimum prices $m_t = \min(m_{t-1},p_t)$. Then:
--
--   1. if $m_0\in\mathbf R_1\cup\mathbf R_2$, then $p_t\ge m_0$ for all $t\ge1$;
--   2. if $m_0\in\mathbf R_3$, then $m_t\in\mathbf R_3$ for all $t\ge0$.
--
--   The state path never leaves the region where it starts: for $m_0\le S$ the minimum price never changes, and for $m_0\ge S$ it may fall but never below $S$. This localizes the possible limits of the price path.
--
--   **Formalization Note** The statement is made for every optimal path. With $q(n) = p_{n+1}$, part 1 reads $q(n)\ge m_0$ for all $n$, and part 2 reads `minPrice m0 q n` $\in[S,\bar p]$ for all $n$ (index $n$ is $m_n$, including $m_0$).
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 13, Proposition 2

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem proposition_2 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) pbar) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar) (hmp : m0 ≤ p0)
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    (m0 ∈ Set.Icc (0 : ℝ) s ∪ Set.Icc s S → ∀ n, q n ≥ m0) ∧
    (m0 ∈ Set.Icc S pbar → ∀ n, minPrice m0 q n ∈ Set.Icc S pbar) := by sorry

end PeakEndPricing.Convergence
