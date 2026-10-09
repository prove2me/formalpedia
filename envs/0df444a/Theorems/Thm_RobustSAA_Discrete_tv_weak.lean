-- Prove2me | Theorems.Thm_RobustSAA_Discrete_tv_weak
-- name    : RobustSAA.Discrete.tv_weak
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:49.166682+00:00
-- url     : https://prove2.me/theorems/c09d8544-5435-4573-8aef-7b347bfe4cce
-- title:
--   §10.6, p. 38 — total variation metrizes weak convergence on finite support
-- statement:
--   Let $F$ be a distribution on a known finite support of $n$ labels, and let $(G_N)$ be any sequence of distributions on that support. Write $p_F$ and $p_{G_N}$ for their probability vectors. Then
--
--   $$
--   G_N\Rightarrow F\quad\Longleftrightarrow\quad d_{\mathrm{TV}}(p_{G_N},p_F)\longrightarrow 0.
--   $$
--
--   This identifies the topology used in uniform consistency with a concrete finite sum and allows the statistic bounds to control weak convergence.
--
--   **Formalization Note** Weak convergence is the topology on `ProbabilityMeasure (Fin n)`, not a separately defined vector topology.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.6, p. 38, first display

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open Filter MeasureTheory

theorem tv_weak (n : ℕ) (G : ℕ → ProbabilityMeasure (Fin n))
    (F : ProbabilityMeasure (Fin n)) :
    Tendsto G atTop (nhds F) ↔
      Tendsto (fun N => dTV (pvec (G N)) (pvec F)) atTop (nhds 0) := by sorry

end RobustSAA.Discrete
