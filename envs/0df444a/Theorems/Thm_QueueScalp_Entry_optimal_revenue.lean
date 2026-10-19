-- Prove2me | Theorems.Thm_QueueScalp_Entry_optimal_revenue
-- name    : QueueScalp.Entry.optimal_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:54.079771+00:00
-- url     : https://prove2.me/theorems/6f43702d-1ce2-402c-9718-dae942fcd0ff
-- title:
--   Optimal revenue in proof of Proposition 3
-- statement:
--   For each demand volume $\Lambda>0$, the paper's two-case expression $\Pi(\Lambda)$ is the attained maximum of $P\lambda q$ over nonnegative prices and compatible customer equilibria. In the all-join regime it is the reduced revenue evaluated at the optimal buying cutoff $\tilde c^*$:
--
--   $$\Pi(\Lambda)=\frac{\Lambda^3\tilde c^*(1-\tilde c^*)}{\mu^2(\mu-\Lambda\tilde c^*)},\qquad \Lambda\le\mu-1/V.$$
--
--   In the balking regime it is the expression (A.4). This identification allows statements about the explicit revenue formula to be transferred to the original optimization problem.
--
--   **Formalization Note** The paper prints $c^F$ in two revenue numerators where the context and substitution require $c^S$; the model uses $c^S$.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), proof of Proposition 3, Online Appendix pp. 2–3 (PDF 35–36), case (i) revenue display and (A.4)

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem optimal_revenue (P : Params) (hS : P.Standing)
    (Lam : ℝ) (hLam : 0 < Lam) :
    IsOptRevenue P Lam (PiStar P Lam) := by sorry
end QueueScalp.Entry
