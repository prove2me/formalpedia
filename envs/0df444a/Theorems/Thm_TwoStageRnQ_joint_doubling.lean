-- Prove2me | Theorems.Thm_TwoStageRnQ_joint_doubling
-- name    : TwoStageRnQ.joint_doubling
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T00:21:52.232209+00:00
-- url     : https://prove2.me/theorems/046e27a3-4136-45ab-93fe-ba6d48d948a5
-- title:
--   Lemma D.3: joint cycle doubling
-- statement:
--   This is Lemma D.3 (joint cycle doubling), eqs. (23)–(24).
--
--   For all setup coefficients $c_1,c_2\ge0$,
--   $$\mathcal J(4c_1,4c_2)\ge2\,\mathcal J(c_1,c_2)-V_0,\qquad \mathcal J(2c_1,2c_2)\ge\tfrac43\,\mathcal J(c_1,c_2)-\tfrac13V_0.$$
--
--   The first inequality compares every pair of cycles with the cycles formed by their even and odd positions; the second follows from the concavity of $t\mapsto\mathcal J(tc_1,tc_2)$. Together with the stagewise bound they give the cancellation behind the constant $5/3$.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Lemma D.3, eq. (D.20); eqs. (23)-(24).

import Definitions.Def_TwoStageRnQ_Analytic

namespace TwoStageRnQ

theorem joint_doubling (P : Params) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    2 * P.Jjoint c1 c2 - P.V0 ≤ P.Jjoint (4 * c1) (4 * c2) ∧
      4 / 3 * P.Jjoint c1 c2 - P.V0 / 3 ≤ P.Jjoint (2 * c1) (2 * c2) := by sorry

end TwoStageRnQ
