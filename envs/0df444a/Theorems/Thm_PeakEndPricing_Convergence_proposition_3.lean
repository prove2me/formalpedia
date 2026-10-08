-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_proposition_3
-- name    : PeakEndPricing.Convergence.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:19.751983+00:00
-- url     : https://prove2.me/theorems/da04b92e-b27c-48bc-92a9-b98539ba3fa4
-- title:
--   Proposition 3 — optimal price paths converge monotonically to p**_λ(m₀), m₀ or S according to the region of m₀
-- statement:
--   Consider the peak-end pricing model under the standing hypotheses of Section 3: Assumption 1 on the base demand $d_0$ (non-negative, bounded, continuous and decreasing on $\mathbf P = [0,\bar p]$, with $d_0(\bar p) = 0$, and base profit $\pi_0(p) = p\,d_0(p)$ non-monotone and strictly concave), $\pi_0$ differentiable on $\mathbf P$, $\lambda\ge\gamma>0$, $\theta\in(0,1]$, $\beta\in(0,1)$. Let $s,S\in\mathbf P$ be the roots of (9) and (10),
--   $$\pi_0'(s) - \lambda(1-\beta(1-\theta))s = 0,\qquad \pi_0'(S) - \gamma(1-\beta)S = 0,$$
--   and $\mathbf R_1 = [0,s]$, $\mathbf R_2 = [s,S]$, $\mathbf R_3 = [S,\bar p]$. Let $(m_0,p_0)$ be an initial state with $m_0,p_0\in\mathbf P$ and $m_0\le p_0$.
--
--   Then an optimal price path from $(m_0,p_0)$ exists, and every optimal price path $\{p_t\}_{t\ge1}$ is monotone (nondecreasing or nonincreasing) and converges:
--
--   1. (a) if $m_0\in\mathbf R_1$: $p_t\to p^{**}_\lambda(m_0)$, the root $x\in\mathbf P$ of
--   $$\pi_0'(x) - \lambda(2-(1-\theta)(1+\beta))x + \lambda\theta m_0 = 0;$$
--   2. (b) if $m_0\in\mathbf R_2$: $p_t\to m_0$;
--   3. (c) if $m_0\in\mathbf R_3$: $p_t\to S$.
--
--   The long-run price depends only on the initial minimum price $m_0$; the initial price $p_0$ shapes the transient path but not its limit. The limits are the steady states identified in Proposition 1.
--
--   **Formalization Note** A path is a sequence $q$ with $q(n) = p_{n+1}$ in $\mathbf P$; it is optimal when its discounted profit equals $J(m_0,p_0)$, defined as a supremum over price sequences. The paper speaks of "the optimal price path" (treating the optimal policy as single-valued); here existence of an optimal path is asserted and monotonicity and convergence are stated for every optimal path. Monotonicity is of $\{p_t\}_{t\ge1}$, not including $p_0$, and is weak. $m_0,p_0\in\mathbf P$ and $m_0\le p_0$ are the paper's state space (p. 12); $s$ and $S$ are carried as given roots in $\mathbf P$; $p^{**}_\lambda(m_0)$ is represented by a root in $\mathbf P$ of (12), which is unique. At the overlaps $m_0 = s$ and $m_0 = S$ the cases agree. Differentiability of $\pi_0$ is an explicit hypothesis that the paper uses implicitly.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 14, Proposition 3

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem proposition_3 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) pbar) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar) (hmp : m0 ≤ p0) :
    (∃ q : ℕ → ℝ, IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) ∧
    ∀ q : ℕ → ℝ, IsOptimalPath pbar d0 lam gam theta beta m0 p0 q →
      (Monotone q ∨ Antitone q) ∧
      (m0 ∈ Set.Icc (0 : ℝ) s → ∃ x ∈ Set.Icc (0 : ℝ) pbar,
        eq12 d0 lam theta beta m0 x ∧ Filter.Tendsto q Filter.atTop (nhds x)) ∧
      (m0 ∈ Set.Icc s S → Filter.Tendsto q Filter.atTop (nhds m0)) ∧
      (m0 ∈ Set.Icc S pbar → Filter.Tendsto q Filter.atTop (nhds S)) := by sorry

end PeakEndPricing.Convergence
