-- Prove2me | Theorems.Thm_ProbMetricStab_General_theorem_2_2
-- name    : ProbMetricStab.General.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:32.462605+00:00
-- url     : https://prove2.me/theorems/f6dd6d45-d034-49dd-ab56-64332039e2d6
-- title:
--   Theorem 2.2, p. 6 — S_U is Berge usc at μ; |v(μ) − v_U(ν)| ≤ L d_{F_U}(μ, ν) and S_U(ν) is a CLM set for d_{F_U}(μ, ν) < δ
-- statement:
--   Let the general assumptions of model (1) hold, let $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, and assume
--
--   1. $S(\mu)$ is nonempty and $\mathcal U\subseteq\mathbb R^m$ is an open bounded neighbourhood of $S(\mu)$;
--   2. if $d\ge1$, the function $x\mapsto\int_\Xi f_0(\xi,x)\mu(d\xi)$ is Lipschitz continuous on $X\cap\operatorname{cl}\mathcal U$;
--   3. the mapping $x\mapsto M_x^{-1}(\mu)$ is metrically regular at each pair $(\bar x,0)$ with $\bar x\in S(\mu)$.
--
--   Then the multifunction $S_{\mathcal U}$ from $(\mathcal P_{\mathcal F_{\mathcal U}},d_{\mathcal F_{\mathcal U}})$ to $\mathbb R^m$ is (Berge) upper semicontinuous at $\mu$, and there are constants $L>0$ and $\delta>0$ such that, whenever $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ and $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\delta$, the values $v(\mu)$, $v_{\mathcal U}(\nu)$ are finite,
--   $$|v(\mu)-v_{\mathcal U}(\nu)|\ \le\ L\,d_{\mathcal F_{\mathcal U}}(\mu,\nu),\tag{4}$$
--   and $S_{\mathcal U}(\nu)$ is a complete local minimizing set of the perturbed problem (3) with respect to $\mathcal U$.
--
--   This is the paper's first quantitative stability result: the minimal information distance $d_{\mathcal F_{\mathcal U}}$ controls the optimal value Lipschitz-wise, and localized solutions persist under small perturbations of the measure.
--
--   **Formalization Note** Berge upper semicontinuity is the classical notion: for every open $O\supseteq S_{\mathcal U}(\mu)$ there is $\varepsilon>0$ with $S_{\mathcal U}(\nu)\subseteq O$ whenever $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ and $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\varepsilon$. The constants $L,\delta$ depend on the model, $\mu$ and $\mathcal U$ only. Finiteness of both values is part of the conclusion. The final clause of the theorem (the case $d=0$) is the separate item `theorem_2_2_d_zero`.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 6, Theorem 2.2, (4)

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem theorem_2_2 {m s d : ℕ} {P : Model m s d}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    P.SUIsBergeUSCAt U μ ∧
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.v μ ≠ ⊤ ∧ P.v μ ≠ ⊥ ∧ P.vU U ν ≠ ⊤ ∧ P.vU U ν ≠ ⊥ ∧
        EReal.abs (P.v μ - P.vU U ν) ≤ ENNReal.ofReal L * P.dFU U μ ν) ∧
      P.IsCLMSet U ν (P.SU U ν) := by sorry

end ProbMetricStab.General
