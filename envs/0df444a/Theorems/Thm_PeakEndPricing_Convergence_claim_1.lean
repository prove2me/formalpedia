-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_claim_1
-- name    : PeakEndPricing.Convergence.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:10.713408+00:00
-- url     : https://prove2.me/theorems/e4878c58-4677-4a27-9368-7638899b9871
-- title:
--   Claim 1 (proof of Prop. 2) — for m₀ ≤ s and m₀ ≤ p₀ ≤ p**_λ(m₀), optimal prices stay ≥ m₀
-- statement:
--   Under the standing hypotheses of Section 3, let $s,S\in\mathbf P$ solve (9) and (10). Let $m_0\in[0,s]$, let $x\in\mathbf P$ solve (12) at $m = m_0$ (so $x = p^{**}_\lambda(m_0)$), and let the initial last price $p_0\in\mathbf P$ satisfy
--   $$m_0 \le p_0 \le x.$$
--   Then every optimal price path $\{p_t\}_{t\ge1}$ from $(m_0,p_0)$ satisfies $p_t \ge m_0$ for all $t$.
--
--   This is the first of two cases in the proof that low initial minimum prices are never undercut (Proposition 2).
--
--   **Formalization Note** The paper states the claim for $(m_0,p_0)\in\overline{\mathbf R}_{1a}$, defined on p. 11 as $\{p\ge p^{**}_\lambda(m),\ m\le s\}$. The proof of Claim 1 ("Because $p_0 < p^{**}_\lambda(m_0)$ …"), the proof of Claim 2 and p. 14 ("for relatively low initial prices, $p_0 < p^{**}_\lambda(m_0)$ (Region $\overline{\mathbf R}_{1a}$)") all use the opposite inequality, so the inequalities in the printed definitions of $\overline{\mathbf R}_{1a}$ and $\overline{\mathbf R}_{1b}$ are swapped. This statement uses the region the proof uses, $m_0\le p_0\le p^{**}_\lambda(m_0)$. The paper speaks of "the" optimal path; the conclusion is stated for every optimal path.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 45, Claim 1 (proof of Proposition 2); regions on p. 11

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem claim_1 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 x : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) s) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar)
    (hx : x ∈ Set.Icc (0 : ℝ) pbar) (hx12 : eq12 d0 lam theta beta m0 x)
    (hmp : m0 ≤ p0) (hpx : p0 ≤ x)
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    ∀ n, m0 ≤ q n := by sorry

end PeakEndPricing.Convergence
