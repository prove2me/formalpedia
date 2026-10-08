-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_claim_5
-- name    : PeakEndPricing.Convergence.claim_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:14.798024+00:00
-- url     : https://prove2.me/theorems/88ec90f9-a372-4fd6-bad3-9adb29780c29
-- title:
--   Claim 5 (proof of Prop. 3) — for p₀ > m₀ ≥ S, the optimal price eventually falls to m₀ or below
-- statement:
--   Under the standing hypotheses of Section 3, let $s,S\in\mathbf P$ solve (9) and (10). Let $m_0,p_0\in\mathbf P$ with
--   $$p_0 > m_0 \ge S.$$
--   Then every optimal price path $\{p_t\}_{t\ge1}$ from $(m_0,p_0)$ reaches the initial minimum price: there is a time $T$ with $p_T\le m_0$.
--
--   For high minimum prices the firm eventually lowers its price to the remembered minimum or below; after that, prices decrease to $S$ (Proposition 3(c)).
--
--   **Formalization Note** "Falls below" is the non-strict $p_T\le m_0$, as the page says ("i.e $p_T\le m_0$"). The conclusion is stated for every optimal path.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 48, Claim 5 (proof of Proposition 3)

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem claim_5 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (s S : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) pbar ∧ eq9 d0 lam theta beta s)
    (hS : S ∈ Set.Icc (0 : ℝ) pbar ∧ eq10 d0 gam beta S)
    (m0 p0 : ℝ) (hm0 : m0 ∈ Set.Icc (0 : ℝ) pbar) (hp0 : p0 ∈ Set.Icc (0 : ℝ) pbar)
    (hpm : p0 > m0) (hmS : m0 ≥ S)
    (q : ℕ → ℝ) (hq : IsOptimalPath pbar d0 lam gam theta beta m0 p0 q) :
    ∃ n, q n ≤ m0 := by sorry

end PeakEndPricing.Convergence
