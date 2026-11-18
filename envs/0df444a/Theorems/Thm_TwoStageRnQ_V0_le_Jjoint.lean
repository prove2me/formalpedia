-- Prove2me | Theorems.Thm_TwoStageRnQ_V0_le_Jjoint
-- name    : TwoStageRnQ.V0_le_Jjoint
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T00:21:50.788231+00:00
-- url     : https://prove2.me/theorems/5f8339f8-49de-4d65-a07e-9d91b873eaf6
-- title:
--   Eq. (22): $V_0\le\mathcal J(c_1,c_2)$
-- statement:
--   This is the third inequality of eq. (22) (from Lemma D.1): the zero-setup value is a lower bound for the joint cycle cost.
--
--   For all setup coefficients $c_1,c_2\ge0$,
--   $$V_0\le\mathcal J(c_1,c_2).$$
--
--   It shows that $v=V_0/\mathcal J$ lies in $[0,1]$ in the interpretation of the two comparisons (Section 6.4).
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Eq. (22), third inequality; Lemma D.1, eq. (D.6).

import Definitions.Def_TwoStageRnQ_Analytic

namespace TwoStageRnQ

theorem V0_le_Jjoint (P : Params) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    P.V0 ≤ P.Jjoint c1 c2 := by sorry

end TwoStageRnQ
