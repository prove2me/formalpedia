-- Prove2me | Theorems.Thm_ProbMetricStab_General_display_5_converse
-- name    : ProbMetricStab.General.display_5_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:09.947981+00:00
-- url     : https://prove2.me/theorems/13c5d4c0-4e72-488c-b34f-f3a001d6d061
-- title:
--   Proof of Theorem 2.2, p. 7 — M_U(ν) ∩ B(x̄, ε̄) ⊆ M_U(μ) + a d_{F_U}(μ, ν)𝔹 whenever d_{F_U}(μ, ν) < ε̄
-- statement:
--   Under the same hypotheses as display (5) — the general assumptions, $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, $\mathcal U$ open with $S(\mu)\subseteq\mathcal U$, $\bar x\in S(\mu)$, and the metric-regularity estimate at $(\bar x,0)$ with constants $a\ge0$, $\varepsilon>0$ — there is $\bar\varepsilon>0$ such that for every $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ with $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\bar\varepsilon$,
--   $$M_{\mathcal U}(\nu)\cap\mathbb B(\bar x,\bar\varepsilon)\ \subseteq\ M_{\mathcal U}(\mu)+a\,d_{\mathcal F_{\mathcal U}}(\mu,\nu)\,\mathbb B.$$
--
--   This is the converse inclusion to (5) established in the proof of Theorem 2.2. Together, the two inclusions give the Lipschitz estimate of the optimal values in Theorem 2.2 and the localization step of Theorem 2.3.
--
--   **Formalization Note** As for (5), $B(\bar x,\bar\varepsilon)$ is the closed ball and "sufficiently small $\bar\varepsilon$" is rendered as the existence of $\bar\varepsilon$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 7, proof of Theorem 2.2 (inclusion after "which is equivalent to the inclusion")

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem display_5_converse {m s d : ℕ} {P : Model m s d} (hP : P.GeneralAssumptions)
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (hμ : μ ∈ P.PFU U)
    (hUo : IsOpen U) (hSU : P.S μ ⊆ U)
    {xbar : EuclideanSpace ℝ (Fin m)} (hxbar : xbar ∈ P.S μ)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hreg : P.MetricRegularityEstimate μ xbar a ε) :
    ∃ εbar : ℝ, 0 < εbar ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal εbar →
      P.MU U ν ∩ closedBall xbar εbar ⊆ enlarge (P.MU U μ) (ENNReal.ofReal a * P.dFU U μ ν) := by sorry

end ProbMetricStab.General
