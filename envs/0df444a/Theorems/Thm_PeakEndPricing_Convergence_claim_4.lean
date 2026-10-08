-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_claim_4
-- name    : PeakEndPricing.Convergence.claim_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:13.717263+00:00
-- url     : https://prove2.me/theorems/9ad123f8-d602-46d4-baa2-45b7102d91b9
-- title:
--   Claim 4 (proof of Prop. 2) — for p₀ > m₀ > S, an optimal price at or below m₀ is at least S
-- statement:
--   Under the standing hypotheses of Section 3, let $s,S\in\mathbf P$ solve (9) and (10). Let $m_0, p_0\in\mathbf P$ with
--   $$p_0 > m_0 > S.$$
--   Then for every optimal price path $\{p_t\}_{t\ge1}$ from $(m_0,p_0)$ and every $t$: if $p_t\le m_0$ then $p_t\ge S$.
--
--   When the initial minimum price is high, the firm may cut prices below it, but never below the threshold $S$; this gives the second part of Proposition 2.
--
--   **Formalization Note** The strict inequalities are as printed. The conclusion is stated for every optimal path.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 47, Claim 4 (proof of Proposition 2)

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem claim_4 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) pbar) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar)
    (hpm : p0 > m0) (hmS : m0 > S)
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    ∀ n, q n ≤ m0 → q n ≥ S := by sorry

end PeakEndPricing.Convergence
