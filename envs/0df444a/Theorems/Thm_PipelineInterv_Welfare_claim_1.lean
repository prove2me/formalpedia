-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_claim_1
-- name    : PipelineInterv.Welfare.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:04.176554+00:00
-- url     : https://prove2.me/theorems/1b4b779a-e84d-4a13-90c2-4cb927e245a5
-- title:
--   Claim 1 (social welfare part), p. 8 — the budget-discretized program loses at most (k−1)ε‖R‖∞
-- statement:
--   Fix an instance with $k$ layers satisfying the standing assumptions of §2, a budget $B\ge 0$ and $\varepsilon>0$. For every tuple $(M_1,\dots,M_{k-1})\in\mathcal F(B,M^0_1,\dots,M^0_{k-1})$ there are natural numbers $n_1,\dots,n_{k-1}$ and matrices $M^\varepsilon_1,\dots,M^\varepsilon_{k-1}$ such that
--
--   1. the budgets $B_t=n_t\varepsilon\in\mathcal B(\varepsilon)$ satisfy $\sum_{t=1}^{k-1}B_t\le B$;
--   2. for every $t$, $M^\varepsilon_t\in\mathcal M$, $M^\varepsilon_t$ agrees with $M^0_t$ on every non-malleable entry, and $c(M^\varepsilon_t,M^0_t)\le B_t$;
--   3. the social welfare satisfies
--   $$W(M^\varepsilon_1,\dots,M^\varepsilon_{k-1})\ \ge\ W(M_1,\dots,M_{k-1})-(k-1)\,\varepsilon\,\|R\|_\infty .$$
--
--   Items 1 and 2 say that $(M^\varepsilon_t)$ is feasible for the budget-discretized Program (4). Since the inequality holds for every feasible tuple, in particular for an optimal one, the optimum of Program (4) is at least $OPT_{SW}-(k-1)\varepsilon\|R\|_\infty$: restricting budget splits to multiples of $\varepsilon$ costs little.
--
--   **Formalization Note.** $OPT_{SW}$, the maximum of Program (1), is replaced by "every feasible tuple", which is equivalent because the maximum is attained (Remark 3, p. 7). Only the social-welfare half of Claim 1 is stated; the maximin half (Program (5)) is not part of this mission. With 0-based transitions `Fin K`, $K=k-1$.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, p. 8, Claim 1 (Program (4) part); proof in Appendix A.1, pp. 24–26

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem claim_1 {w K : ℕ} (I : Instance w K) (hI : I.Standing) (B ε : ℝ) (hB : 0 ≤ B)
    (hε : 0 < ε) (M : Fin K → Matrix (Fin w) (Fin w) ℝ) (hM : Feasible I B M) :
    ∃ (n : Fin K → ℕ) (Meps : Fin K → Matrix (Fin w) (Fin w) ℝ),
      ∑ t, (n t : ℝ) * ε ≤ B ∧
      (∀ t, Prog7Feasible I t ((n t : ℝ) * ε) (Meps t)) ∧
      welfare I M - (K : ℝ) * ε * supNorm I.R ≤ welfare I Meps := by sorry

end PipelineInterv.Welfare
