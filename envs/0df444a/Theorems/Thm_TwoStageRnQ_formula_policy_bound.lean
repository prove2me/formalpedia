-- Prove2me | Theorems.Thm_TwoStageRnQ_formula_policy_bound
-- name    : TwoStageRnQ.formula_policy_bound
-- status  : Proved
-- author  : @beatlesmania
-- created : 2026-11-17T00:21:51.731915+00:00
-- url     : https://prove2.me/theorems/02933df8-e997-4343-b710-fad40d477189
-- title:
--   Lemma D.2 (formula form): best exact classical formula is at most $\mathcal J(k_1,k_2)$
-- statement:
--   This is the analytic form of Lemma D.2: the exact classical cost formula of Proposition 1, minimized over integer controls, is at most the joint cycle cost.
--
--   For every instance,
--   $$\inf_{R_1,R_2\in\mathbb Z,\ Q,n\ge1}\Big\{\frac{k_1}{Q}+\frac{k_2}{nQ}+I_{n,Q}(R_1+Q,R_2-R_1)\Big\}\le\mathcal J(k_1,k_2).$$
--
--   With Proposition 1 it yields the first inequality of eq. (22) for $\lambda>0$.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Lemma D.2, eqs. (D.11)-(D.14); eq. (D.28).

import Definitions.Def_TwoStageRnQ_Analytic

namespace TwoStageRnQ

theorem formula_policy_bound (P : Params) :
    (⨅ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2)
      ≤ P.Jjoint P.k1 P.k2 := by sorry

end TwoStageRnQ
