-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_claim_2
-- name    : PeakEndPricing.Convergence.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:16.941978+00:00
-- url     : https://prove2.me/theorems/c7c1f592-76d8-4377-89be-483fd1d9fc45
-- title:
--   Claim 2 (proof of Prop. 2) — for m₀ ≤ s and p₀ ≥ p**_λ(m₀), optimal prices stay ≥ p**_λ(m₀) ≥ m₀
-- statement:
--   Under the standing hypotheses of Section 3, let $s,S\in\mathbf P$ solve (9) and (10). Let $m_0\in[0,s]$, let $x\in\mathbf P$ solve (12) at $m = m_0$ (so $x = p^{**}_\lambda(m_0)$), and let $p_0\in\mathbf P$ satisfy $m_0\le p_0$ and $x\le p_0$. Then
--   $$x \ge m_0,$$
--   and every optimal price path $\{p_t\}_{t\ge1}$ from $(m_0,p_0)$ satisfies $p_t\ge x$ for all $t$.
--
--   This is the second case in the proof of Proposition 2: from a high initial price, optimal prices never drop below the steady-state price $p^{**}_\lambda(m_0)$, hence never below $m_0$.
--
--   **Formalization Note** The paper states the claim for $(m_0,p_0)\in\overline{\mathbf R}_{1b}$, printed on p. 11 as $\{p\le p^{**}_\lambda(m),\ m\le s, p\}$; the proof uses "$p_0 > p^{**}_\lambda(m_0)$", so the printed inequality is swapped (see Claim 1) and this statement uses $p_0\ge p^{**}_\lambda(m_0)$, $m_0\le p_0$. The page writes $p^{**}(m_0)$ for $p^{**}_\lambda(m_0)$. The conclusion is stated for every optimal path.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 45, Claim 2 (proof of Proposition 2); regions on p. 11

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem claim_2 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 x : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) s) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar)
    (hx : x ∈ Set.Icc (0 : ℝ) pbar) (hx12 : eq12 d0 lam theta beta m0 x)
    (hmp : m0 ≤ p0) (hxp : x ≤ p0) :
    m0 ≤ x ∧ ∀ q : ℕ → ℝ, IsOptimalPath pbar d0 lam gam theta beta m0 p0 q → ∀ n, x ≤ q n := by sorry

end PeakEndPricing.Convergence
