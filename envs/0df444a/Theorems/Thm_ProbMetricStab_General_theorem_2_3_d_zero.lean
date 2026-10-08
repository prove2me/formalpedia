-- Prove2me | Theorems.Thm_ProbMetricStab_General_theorem_2_3_d_zero
-- name    : ProbMetricStab.General.theorem_2_3_d_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:28.402244+00:00
-- url     : https://prove2.me/theorems/0baa1b20-52a4-43e1-8a41-cd7ae58f4a8c
-- title:
--   Theorem 2.3, (6), p. 8, case d = 0 — ∅ ≠ S_U(ν) ⊆ S(μ) + Ψ(L̂ d_{F_U}(μ, ν))𝔹 for each ν ∈ P_{F_U}
-- statement:
--   Consider model (1) without stochastic constraints ($d=0$) and assume the hypotheses of Theorem 2.2 (the general assumptions, $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, $S(\mu)\neq\emptyset$, $\mathcal U$ an open bounded neighbourhood of $S(\mu)$). Let $\psi$ be the growth function of problem (1) on $\operatorname{cl}\mathcal U$,
--   $$\psi(\tau)=\inf\Big\{\int_\Xi f_0(\xi,x)\mu(d\xi)-v(\mu)\ :\ d(x,S(\mu))\ge\tau,\ x\in M_{\mathcal U}(\mu)\Big\}\quad(\tau\ge0),$$
--   $\psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\}$ and $\Psi(\eta)=\eta+\psi^{-1}(\eta)$. Then there is a constant $\hat L\ge1$ such that for **each** $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$
--   $$\emptyset\ne S_{\mathcal U}(\nu)\ \subseteq\ S(\mu)+\Psi\big(\hat L\,d_{\mathcal F_{\mathcal U}}(\mu,\nu)\big)\,\mathbb B.\tag{6}$$
--
--   This is Theorem 2.3 exactly as printed, in the case $d=0$, where it holds for all perturbations $\nu$ without any smallness condition: the solution sets move by at most $\Psi$ of the minimal information distance.
--
--   **Formalization Note** $\Psi$, $\psi^{-1}$ and $d_{\mathcal F_{\mathcal U}}$ take values in $[0,\infty]$; when $d_{\mathcal F_{\mathcal U}}(\mu,\nu)=\infty$ the inclusion is trivial. The paper's "min" in $\psi$ is read as an infimum ($+\infty$ over the empty set). For $d\ge1$ the printed "for each $\nu$" fails; see the goal theorem `theorem_2_3`.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 8, Theorem 2.3, (6), and its proof ("In case that d = 0 ...")

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem theorem_2_3_d_zero {m s : ℕ} {P : Model m s 0}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ ν ∈ P.PFU U,
      (P.SU U ν).Nonempty ∧
      P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by sorry

end ProbMetricStab.General
