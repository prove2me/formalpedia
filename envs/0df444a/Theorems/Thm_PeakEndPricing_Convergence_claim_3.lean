-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_claim_3
-- name    : PeakEndPricing.Convergence.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:18.56014+00:00
-- url     : https://prove2.me/theorems/f774a03e-dd7f-4d55-9508-d813ee57725e
-- title:
--   Claim 3 (proof of Prop. 2) — for m₀ ∈ R₂ = [s, S], optimal prices stay ≥ m₀
-- statement:
--   Under the standing hypotheses of Section 3, let $s,S\in\mathbf P$ solve (9) and (10). Let $m_0\in\mathbf R_2 = [s,S]$ and $p_0\in\mathbf P$ with $m_0\le p_0$. Then every optimal price path $\{p_t\}_{t\ge1}$ from $(m_0,p_0)$ satisfies
--   $$p_t\ge m_0 \quad\text{for all } t.$$
--
--   For intermediate minimum prices the firm never undercuts the remembered minimum; together with Claims 1–2 this is the first part of Proposition 2.
--
--   **Formalization Note** $m_0\le p_0$ is the paper's state space (p. 12) and $p_0\in\mathbf P$ is implicit. The conclusion is stated for every optimal path.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 46, Claim 3 (proof of Proposition 2)

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem claim_3 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm0 : m0 ∈ Set.Icc s S) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar) (hmp : m0 ≤ p0)
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    ∀ n, m0 ≤ q n := by sorry

end PeakEndPricing.Convergence
