-- Prove2me | Theorems.Thm_ProbMetricStab_General_proposition_2_1_closed_graph
-- name    : ProbMetricStab.General.proposition_2_1_closed_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:15.176107+00:00
-- url     : https://prove2.me/theorems/3981b332-b457-4c1a-8d3a-da89943e3c5e
-- title:
--   Proposition 2.1, p. 5 — the graph of ν ↦ M_U(ν) from (P_{F_U}, d_{F_U}) into ℝ^m is closed
-- statement:
--   Let the general assumptions of model (1) hold and let $\mathcal U\subseteq\mathbb R^m$ be nonempty. Let $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$, let $(\nu_n)$ be a sequence in $\mathcal P_{\mathcal F_{\mathcal U}}$ with $d_{\mathcal F_{\mathcal U}}(\nu,\nu_n)\to0$, and let $x_n\in M_{\mathcal U}(\nu_n)$ for every $n$ with $x_n\to x$. Then
--   $$x\in M_{\mathcal U}(\nu).$$
--
--   This is the second assertion of Proposition 2.1: the set-valued map $\nu\mapsto M_{\mathcal U}(\nu)$ has a closed graph. Together with the boundedness of $\mathcal U$ it gives the upper semicontinuity of the localized feasible sets used in the proof of Theorem 2.2.
--
--   **Formalization Note** Closedness of the graph is stated sequentially, which is equivalent because $d_{\mathcal F_{\mathcal U}}$ is an extended pseudometric on $\mathcal P_{\mathcal F_{\mathcal U}}$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 5, Proposition 2.1 (second assertion)

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem proposition_2_1_closed_graph {m s d : ℕ} {P : Model m s d} (hP : P.GeneralAssumptions)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : U.Nonempty)
    {ν : Measure ↥P.Ξ} (hν : ν ∈ P.PFU U)
    (νn : ℕ → Measure ↥P.Ξ) (hνn : ∀ n, νn n ∈ P.PFU U)
    (hνlim : Tendsto (fun n => P.dFU U ν (νn n)) atTop (𝓝 0))
    {x : EuclideanSpace ℝ (Fin m)} (xn : ℕ → EuclideanSpace ℝ (Fin m))
    (hxn : ∀ n, xn n ∈ P.MU U (νn n)) (hx : Tendsto xn atTop (𝓝 x)) :
    x ∈ P.MU U ν := by sorry

end ProbMetricStab.General
