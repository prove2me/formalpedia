-- Prove2me | Theorems.Thm_QueueScalp_Entry_revenue_limits
-- name    : QueueScalp.Entry.revenue_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:56.466515+00:00
-- url     : https://prove2.me/theorems/44aeb554-974c-4960-a5f3-39189b7cee86
-- title:
--   Revenue minus cost at extreme demand
-- statement:
--   Under the model assumptions with a positive cost rate $k$, the scalper's maximum revenue less cost tends to a negative value at both extreme demand levels:
--
--   $$\lim_{\Lambda\to0+}(\Pi(\Lambda)-k)=-k<0,\qquad \lim_{\Lambda\to\infty}(\Pi(\Lambda)-k)=-k<0.$$
--
--   These limits supply the low-demand and high-demand nonentry sides of Proposition 4.
--
--   **Formalization Note** The limit statement uses the paper's explicit revenue function. The separate optimal-revenue milestone identifies it with the attained maximum in the customer-equilibrium model.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), proof of Proposition 4, Online Appendix p. 3 (PDF 36), two limit displays

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem revenue_limits (P : Params) (hS : P.Standing) (hk : 0 < P.k) :
    Filter.Tendsto (fun Lam : ℝ => PiStar P Lam - P.k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-P.k)) ∧
    Filter.Tendsto (fun Lam : ℝ => PiStar P Lam - P.k)
      Filter.atTop (nhds (-P.k)) := by sorry
end QueueScalp.Entry
