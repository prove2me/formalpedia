-- Prove2me | Theorems.Thm_ProbMetricStab_General_theorem_2_2_d_zero
-- name    : ProbMetricStab.General.theorem_2_2_d_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:25.139555+00:00
-- url     : https://prove2.me/theorems/84f689dd-71c9-48ca-a4ae-6daec723604a
-- title:
--   Theorem 2.2, last sentence, p. 6 — for d = 0, |v(μ) − v_U(ν)| ≤ d_{F_U}(μ, ν) for all ν ∈ P_{F_U}
-- statement:
--   Consider model (1) without stochastic constraints ($d=0$). Assume the hypotheses of Theorem 2.2: the general assumptions, $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, $S(\mu)\ne\emptyset$, $\mathcal U$ an open bounded neighbourhood of $S(\mu)$ (the Lipschitz and metric-regularity conditions are automatic or void when $d=0$). Then for every $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ the values $v(\mu)$ and $v_{\mathcal U}(\nu)$ are finite and
--   $$|v(\mu)-v_{\mathcal U}(\nu)|\ \le\ d_{\mathcal F_{\mathcal U}}(\mu,\nu).$$
--
--   This is the last sentence of Theorem 2.2: in the absence of constraints the estimate (4) holds with $L=1$ and globally on $\mathcal P_{\mathcal F_{\mathcal U}}$, with no restriction on the distance between $\mu$ and $\nu$.
--
--   **Formalization Note** The finiteness of $v(\mu)$ and $v_{\mathcal U}(\nu)$, implicit on the page (which writes a real inequality), is part of the conclusion, so the extended-real difference never takes the form $\infty-\infty$. The hypotheses are the bundle of Theorem 2.2's assumptions instantiated at $d=0$; condition (ii) is void and (iii) is part of the bundle as on the page.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 6, Theorem 2.2 ("In case d = 0, the estimate (4) is valid with L = 1 and for all ν ∈ P_{F_U}")

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ProbMetricStab.General

theorem theorem_2_2_d_zero {m s : ℕ} {P : Model m s 0}
    {U : Set (EuclideanSpace ℝ (Fin m))} {μ : Measure ↥P.Ξ} (h : P.Thm22Assumptions U μ) :
    ∀ ν ∈ P.PFU U,
      P.v μ ≠ ⊤ ∧ P.v μ ≠ ⊥ ∧ P.vU U ν ≠ ⊤ ∧ P.vU U ν ≠ ⊥ ∧
      EReal.abs (P.v μ - P.vU U ν) ≤ P.dFU U μ ν := by sorry

end ProbMetricStab.General
