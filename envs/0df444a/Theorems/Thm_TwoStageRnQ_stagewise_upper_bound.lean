-- Prove2me | Theorems.Thm_TwoStageRnQ_stagewise_upper_bound
-- name    : TwoStageRnQ.stagewise_upper_bound
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:21:51.136752+00:00
-- url     : https://prove2.me/theorems/2c4da559-e178-458c-86c5-d3637da55e35
-- title:
--   Eq. (D.18): $\mathcal J(c_1,c_2)\le B_1(c_1)+B_2(c_2)$
-- statement:
--   This is eq. (D.18), the second inequality of eq. (22): the joint value is bounded by two separate cycle calculations.
--
--   1. For all integers $m_1,m_2\ge1$,
--   $$V_{m_1,m_2}\le H_0+\mathcal H_{m_1}(P)+\mathcal H_{m_2}(F_{\mathrm{up}}).$$
--   2. For all setup coefficients $c_1,c_2\ge0$,
--   $$\mathcal J(c_1,c_2)\le B_1(c_1)+B_2(c_2).$$
--
--   It links the joint calculation, which upper-bounds classical policies, to the single-stage benchmarks that appear in the lower bound $L_{\mathrm{two}}$.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Eq. (22), second inequality; eq. (D.18).

import Definitions.Def_TwoStageRnQ_Analytic

namespace TwoStageRnQ

theorem stagewise_upper_bound (P : Params) :
    (∀ m1 m2 : ℕ+, P.Vjoint m1 m2 ≤ P.H0 + latInf m1 P.lossDown + latInf m2 P.lossUp) ∧
    ∀ c1 c2 : ℝ, 0 ≤ c1 → 0 ≤ c2 → P.Jjoint c1 c2 ≤ P.B1 c1 + P.B2 c2 := by sorry

end TwoStageRnQ
