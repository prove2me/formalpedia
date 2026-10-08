-- Prove2me | Theorems.Thm_QualityEncroach_FixedCost_subgame_high
-- name    : QualityEncroach.FixedCost.subgame_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:55.134897+00:00
-- url     : https://prove2.me/theorems/d14946e4-8a75-4492-aa2b-d151cf195913
-- title:
--   §6.2, p. 36 — high direct quality: backward-induction subgame and profit
-- statement:
--   Fix $k>0$, $c\ge0$, $0<t\le1$, and an encroachment-feasible quality $u>(8-3t)c/(8-5t)$. In the high-direct-quality branch, the manufacturer's final quantity response maximizes her payoff among nonnegative direct quantities. When the retailer's displayed interior reply is nonnegative and induces positive direct sales, it maximizes the retailer's payoff among nonnegative orders. The displayed wholesale price maximizes the corresponding interior manufacturer profit over wholesale prices with these same feasibility properties.
--
--   At that wholesale price, the actions and the manufacturer's resulting profit are
--
--   $$w=\frac{tu}{2}-\frac{ct^2}{2(8-5t)},\quad q_R=\frac{2c}{(8-5t)u},\quad q_M=\frac12-\frac{c(8-3t)}{2(8-5t)u},\quad \Pi_M=\Pi_{\mathrm{Hi}}(k,c,t,u).$$
--
--   These backward-induction identities connect Claim 3's reduced profit to the game's action sequence.
--
--   **Formalization Note** The optimization claims are restricted to the interior encroaching branch; the full game also admits no-encroachment histories.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 36, first block of e-Companion §Encroachment with Fixed Cost of Quality

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

namespace QualityEncroach.FixedCost

/-- Backward-induction formulas for the `0 < t ≤ 1` encroaching branch,
including the stage-3 and stage-2 best replies and the first-stage price
within that branch (Ha, Long and Nasiry, p. 36). -/
theorem subgame_high (k c t u : ℝ) (hk : 0 < k) (hc : 0 ≤ c)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hu : (8 - 3 * t) * c / (8 - 5 * t) < u) :
    (∀ w qR qM : ℝ, 0 ≤ qR → 0 ≤ qM →
      mfrPayoff k c ⟨w, u, t, qR, qM⟩ ≤
        mfrPayoff k c ⟨w, u, t, qR, qMReplyHi c t u qR⟩) ∧
    (∀ w : ℝ, 0 ≤ qRHiAt c w t u →
      0 < qMReplyHi c t u (qRHiAt c w t u) →
      ∀ qR : ℝ, 0 ≤ qR →
        QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qR, qMReplyHi c t u qR⟩ ≤
          QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qRHiAt c w t u,
            qMReplyHi c t u (qRHiAt c w t u)⟩) ∧
    (∀ w : ℝ, 0 ≤ qRHiAt c w t u →
      0 < qMReplyHi c t u (qRHiAt c w t u) →
      mfrPayoff k c ⟨w, u, t, qRHiAt c w t u,
        qMReplyHi c t u (qRHiAt c w t u)⟩ ≤
        mfrPayoff k c ⟨wHi c t u, u, t, qRHi c t u, qMHi c t u⟩) ∧
    qRHiAt c (wHi c t u) t u = qRHi c t u ∧
    qMReplyHi c t u (qRHi c t u) = qMHi c t u ∧
    0 < qMHi c t u ∧
    mfrPayoff k c ⟨wHi c t u, u, t, qRHi c t u, qMHi c t u⟩ =
      PiHi k c t u := by sorry

end QualityEncroach.FixedCost
