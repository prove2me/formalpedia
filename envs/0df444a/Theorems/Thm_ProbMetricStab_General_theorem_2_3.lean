-- Prove2me | Theorems.Thm_ProbMetricStab_General_theorem_2_3
-- name    : ProbMetricStab.General.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:28.198859+00:00
-- url     : https://prove2.me/theorems/9d9bb6ea-e401-45da-9514-b4c5fca88eec
-- title:
--   Theorem 2.3, (6), p. 8, for d_{F_U}(μ, ν) < δ — ∅ ≠ S_U(ν) ⊆ S(μ) + Ψ(L̂ d_{F_U}(μ, ν))𝔹
-- statement:
--   Let the assumptions of Theorem 2.2 hold: the general assumptions of model (1), $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, and
--
--   1. $S(\mu)$ is nonempty and $\mathcal U\subseteq\mathbb R^m$ is an open bounded neighbourhood of $S(\mu)$;
--   2. if $d\ge1$, $x\mapsto\int_\Xi f_0(\xi,x)\mu(d\xi)$ is Lipschitz continuous on $X\cap\operatorname{cl}\mathcal U$;
--   3. $x\mapsto M^{-1}_x(\mu)$ is metrically regular at each pair $(\bar x,0)$ with $\bar x\in S(\mu)$.
--
--   Let $\psi(\tau)=\inf\{\int_\Xi f_0(\xi,x)\mu(d\xi)-v(\mu):d(x,S(\mu))\ge\tau,\ x\in M_{\mathcal U}(\mu)\}$ ($\tau\ge0$) be the growth function of problem (1) on $\operatorname{cl}\mathcal U$, $\psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\}$, and $\Psi(\eta)=\eta+\psi^{-1}(\eta)$. Then there are constants $\hat L\ge1$ and $\delta>0$ such that for each $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ with $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\delta$,
--   $$\emptyset\ne S_{\mathcal U}(\nu)\ \subseteq\ S(\mu)+\Psi\big(\hat L\,d_{\mathcal F_{\mathcal U}}(\mu,\nu)\big)\,\mathbb B.\tag{6}$$
--
--   This is the paper's quantitative stability theorem for solution sets: the localized solution sets of the perturbed problem stay within $\Psi$ of the minimal information distance from the original solution set, and the modulus $\Psi$ is governed by the growth of the objective near $S(\mu)$. For $k$-th order growth $\psi(\tau)=\gamma\tau^k$ it gives Hölder continuity of $S_{\mathcal U}$ at $\mu$ with rate $1/k$ (Remark 2.4).
--
--   **Formalization Note** The page states (6) "for each $\nu\in\mathcal P_{\mathcal F,\mathcal U}$". For $d\ge1$ this is false: with $X=[0,1]$, $d=1$, $f_0(\xi,x)=x$, $f_1(\xi,x)=\xi-x$, $\mu=\delta_0$, $\mathcal U=(-\tfrac12,\tfrac12)$, all hypotheses hold, but $\nu=\delta_1$ gives $M_{\mathcal U}(\nu)=\emptyset$ and so $S_{\mathcal U}(\nu)=\emptyset$. The proof argues "as in the proof of Theorem 2.2", which needs $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\delta$. The statement here is therefore the δ-local form the proof establishes; the printed all-$\nu$ form is the separate item `theorem_2_3_d_zero` for $d=0$, where it is true. $\Psi$, $\psi^{-1}$ and $d_{\mathcal F_{\mathcal U}}$ take values in $[0,\infty]$, $\psi$ is an infimum in $\overline{\mathbb R}$ ($+\infty$ when no feasible point is $\tau$-far from $S(\mu)$), and $d(x,A)$ is the extended distance ($+\infty$ for $A=\emptyset$).
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 8, Theorem 2.3, (6) (δ-local form established by the proof; the printed "for each ν" fails for d ≥ 1)

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem theorem_2_3 {m s d : ℕ} {P : Model m s d}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∃ Lhat δ : ℝ, 1 ≤ Lhat ∧ 0 < δ ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal δ →
      (P.SU U ν).Nonempty ∧
      P.SU U ν ⊆ enlarge (P.S μ) (P.Ψ U μ (ENNReal.ofReal Lhat * P.dFU U μ ν)) := by sorry

end ProbMetricStab.General
