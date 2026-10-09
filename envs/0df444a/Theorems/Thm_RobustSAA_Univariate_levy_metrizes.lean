-- Prove2me | Theorems.Thm_RobustSAA_Univariate_levy_metrizes
-- name    : RobustSAA.Univariate.levy_metrizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:55.252733+00:00
-- url     : https://prove2.me/theorems/d3731819-9466-42d9-8b5a-1ff778c4e859
-- title:
--   §10.7, p. 38 — on ℝ the Lévy metric metrizes weak convergence
-- statement:
--   Let $F$ and $G_1,G_2,\dots$ be probability distributions on $\mathbb R$, with cdfs $F(t)$ and $G_N(t)$, and let
--
--   $$d_{\text{Lévy}}(G,G')=\inf\{\epsilon>0: G(\xi-\epsilon)-\epsilon\le G'(\xi)\le G(\xi+\epsilon)+\epsilon\ \ \forall\xi\in\mathbb R\}.$$
--
--   Then $G_N$ converges weakly to $F$ if and only if
--
--   $$d_{\text{Lévy}}(G_N,F)\longrightarrow0 .$$
--
--   This is the classical fact, quoted at the start of the proof of Theorem 5, that lets weak convergence on the line be checked through cdfs.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, first sentence of the proof of Theorem 5, p. 38

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 38: on `ℝ` the Lévy metric metrizes weak convergence. -/
theorem levy_metrizes (G : ℕ → ProbabilityMeasure ℝ) (F : ProbabilityMeasure ℝ) :
    Tendsto G atTop (nhds F) ↔
      Tendsto (fun N => levyDist (cdfOf (G N)) (cdfOf F)) atTop (nhds 0) := by sorry

end RobustSAA.Univariate
