-- Prove2me | Theorems.Thm_QualityEncroach_FixedCost_subgame_low
-- name    : QualityEncroach.FixedCost.subgame_low
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:49.408244+00:00
-- url     : https://prove2.me/theorems/9317029e-fee3-4057-9fab-9f45240add33
-- title:
--   §6.2, p. 36 — low direct quality: backward-induction subgame and (22)
-- statement:
--   Fix $k>0$, $c\ge0$, $t\ge1$, and an encroachment-feasible quality $(8t-3)c<(6t-3)u$. In the low-direct-quality branch, the manufacturer's final quantity response is optimal among nonnegative direct quantities. Whenever the displayed retailer reply is nonnegative and induces positive direct sales, it is optimal among nonnegative retailer orders. The displayed wholesale price maximizes the interior manufacturer profit among wholesale prices with these feasibility properties.
--
--   At that price,
--
--   $$w=\frac{(8t^2-6t+1)u-c}{2(8t-5)},\quad q_R=\frac{2c}{(8t-5)u}+\frac{2(t-1)}{8t-5},\quad q_M=\frac{6t-3}{2(8t-5)}-\frac{(8t-3)c}{2(8t-5)u},\quad \Pi_M=\Pi_{\mathrm{Lo}}(k,c,t,u).$$
--
--   This links equation (22) to the game's backward-induction actions.
--
--   **Formalization Note** The wholesale optimization is over the interior encroaching branch, not over no-encroachment outcomes.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 36, second block and equation (22)

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

namespace QualityEncroach.FixedCost

/-- Backward-induction formulas for the `1 ≤ t` encroaching branch,
including equation (22) (Ha, Long and Nasiry, p. 36). -/
theorem subgame_low (k c t u : ℝ) (hk : 0 < k) (hc : 0 ≤ c)
    (ht : 1 ≤ t) (hu : (8 * t - 3) * c < (6 * t - 3) * u) :
    (∀ w qR qM : ℝ, 0 ≤ qR → 0 ≤ qM →
      mfrPayoff k c ⟨w, u, t, qR, qM⟩ ≤
        mfrPayoff k c ⟨w, u, t, qR, qMReplyLo c u qR⟩) ∧
    (∀ w : ℝ, 0 ≤ qRLoAt c w t u →
      0 < qMReplyLo c u (qRLoAt c w t u) →
      ∀ qR : ℝ, 0 ≤ qR →
        QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qR, qMReplyLo c u qR⟩ ≤
          QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qRLoAt c w t u,
            qMReplyLo c u (qRLoAt c w t u)⟩) ∧
    (∀ w : ℝ, 0 ≤ qRLoAt c w t u →
      0 < qMReplyLo c u (qRLoAt c w t u) →
      mfrPayoff k c ⟨w, u, t, qRLoAt c w t u,
        qMReplyLo c u (qRLoAt c w t u)⟩ ≤
        mfrPayoff k c ⟨wLo c t u, u, t, qRLo c t u, qMLo c t u⟩) ∧
    qRLoAt c (wLo c t u) t u = qRLo c t u ∧
    qMReplyLo c u (qRLo c t u) = qMLo c t u ∧
    0 < qMLo c t u ∧
    mfrPayoff k c ⟨wLo c t u, u, t, qRLo c t u, qMLo c t u⟩ =
      PiLo k c t u := by sorry

end QualityEncroach.FixedCost
