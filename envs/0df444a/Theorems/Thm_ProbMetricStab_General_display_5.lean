-- Prove2me | Theorems.Thm_ProbMetricStab_General_display_5
-- name    : ProbMetricStab.General.display_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:19.729989+00:00
-- url     : https://prove2.me/theorems/365fef9e-54b3-460b-89b1-79c8ee043a17
-- title:
--   (5), proof of Theorem 2.2, p. 6 — M_U(μ) ∩ B(x̄, ε̄) ⊆ M_U(ν) + a d_{F_U}(μ, ν)𝔹 whenever d_{F_U}(μ, ν) < ε̄
-- statement:
--   Let the general assumptions of model (1) hold, let $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, let $\mathcal U$ be open with $S(\mu)\subseteq\mathcal U$, and let $\bar x\in S(\mu)$. Suppose the metric-regularity estimate holds at $(\bar x,0)$ with constants $a\ge0$ and $\varepsilon>0$: for all $x\in X\cap\mathbb B(\bar x,\varepsilon)$ and $y\in\mathbb R^d$ with $\max_j|y_j|\le\varepsilon$,
--   $$d(x,M_y(\mu))\le a\max_{j=1,\dots,d}\max\Big\{0,\int_\Xi f_j(\xi,x)\mu(d\xi)-y_j\Big\}.$$
--   Then there is $\bar\varepsilon>0$ such that for every $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ with $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\bar\varepsilon$,
--   $$M_{\mathcal U}(\mu)\cap\mathbb B(\bar x,\bar\varepsilon)\ \subseteq\ M_{\mathcal U}(\nu)+a\,d_{\mathcal F_{\mathcal U}}(\mu,\nu)\,\mathbb B,$$
--   where $\mathbb B$ is the closed unit ball of $\mathbb R^m$.
--
--   This lower-semicontinuity property of the localized feasible-set map $M_{\mathcal U}$ at $(\bar x,\mu)$ is the key step in the proof of Theorem 2.2: it turns metric regularity of the constraints into a Lipschitz-type estimate for the feasible sets in terms of the distance $d_{\mathcal F_{\mathcal U}}$.
--
--   **Formalization Note** The ball $B(\bar x,\bar\varepsilon)$ of display (5) is read as the closed ball, like $\mathbb B(\bar x,\bar\varepsilon)$ elsewhere on the page; the existence of $\bar\varepsilon$ does not depend on this choice. "$\bar\varepsilon>0$ sufficiently small" is rendered as the existence of $\bar\varepsilon$. The constant $a$ is the one from the metric-regularity estimate, as on the page. $A+r\mathbb B$ is the set of points at distance at most $r$ from a point of $A$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), pp. 6–7, display (5) in the proof of Theorem 2.2

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem display_5 {m s d : ℕ} {P : Model m s d} (hP : P.GeneralAssumptions)
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (hμ : μ ∈ P.PFU U)
    (hUo : IsOpen U) (hSU : P.S μ ⊆ U)
    {xbar : EuclideanSpace ℝ (Fin m)} (hxbar : xbar ∈ P.S μ)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hreg : P.MetricRegularityEstimate μ xbar a ε) :
    ∃ εbar : ℝ, 0 < εbar ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal εbar →
      P.MU U μ ∩ closedBall xbar εbar ⊆ enlarge (P.MU U ν) (ENNReal.ofReal a * P.dFU U μ ν) := by sorry

end ProbMetricStab.General
