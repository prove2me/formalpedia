-- Prove2me | Theorems.Thm_ProbMetricStab_General_proposition_2_1_lsc
-- name    : ProbMetricStab.General.proposition_2_1_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:04.673378+00:00
-- url     : https://prove2.me/theorems/071701e9-dbc1-4985-a778-ae2e487bb627
-- title:
--   Proposition 2.1, p. 5 — (x, ν) ↦ ∫ f_j(ξ, x) ν(dξ) is lower semicontinuous on (X ∩ cl U) × (P_{F_U}, d_{F_U})
-- statement:
--   Let the general assumptions of model (1) hold and let $\mathcal U\subseteq\mathbb R^m$ be nonempty. Fix $j\in\{0,\dots,d\}$ and $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$. Let $(x_n)$ be a sequence in $X\cap\operatorname{cl}\mathcal U$ with $x_n\to x$, and let $(\nu_n)$ be a sequence in $\mathcal P_{\mathcal F_{\mathcal U}}$ with $d_{\mathcal F_{\mathcal U}}(\nu,\nu_n)\to0$. Then
--   $$\int_\Xi f_j(\xi,x)\,\nu(d\xi)\ \le\ \liminf_{n\to\infty}\int_\Xi f_j(\xi,x_n)\,\nu_n(d\xi).$$
--
--   This is the first assertion of Proposition 2.1: the map $(x,\nu)\mapsto\int_\Xi f_j(\xi,x)\nu(d\xi)$ from $(X\cap\operatorname{cl}\mathcal U)\times(\mathcal P_{\mathcal F_{\mathcal U}},d_{\mathcal F_{\mathcal U}})$ to $\overline{\mathbb R}$ is lower semicontinuous. It yields the closedness of the constraint sets and the existence of localized solutions used throughout Section 2.
--
--   **Formalization Note** Lower semicontinuity is stated sequentially. $d_{\mathcal F_{\mathcal U}}$ is an extended pseudometric on $\mathcal P_{\mathcal F_{\mathcal U}}$, so the product space is first countable and sequential lower semicontinuity is lower semicontinuity. The limit point $x$ lies in $X\cap\operatorname{cl}\mathcal U$ automatically (both sets are closed). The liminf is taken in $\overline{\mathbb R}$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 5, Proposition 2.1 (first assertion)

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem proposition_2_1_lsc {m s d : ℕ} {P : Model m s d} (hP : P.GeneralAssumptions)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : U.Nonempty) (j : Fin (d + 1))
    {ν : Measure ↥P.Ξ} (hν : ν ∈ P.PFU U)
    {x : EuclideanSpace ℝ (Fin m)} (xn : ℕ → EuclideanSpace ℝ (Fin m))
    (hxn : ∀ n, xn n ∈ P.X ∩ closure U) (hx : Tendsto xn atTop (𝓝 x))
    (νn : ℕ → Measure ↥P.Ξ) (hνn : ∀ n, νn n ∈ P.PFU U)
    (hνlim : Tendsto (fun n => P.dFU U ν (νn n)) atTop (𝓝 0)) :
    P.integral ν j x ≤ liminf (fun n => P.integral (νn n) j (xn n)) atTop := by sorry

end ProbMetricStab.General
