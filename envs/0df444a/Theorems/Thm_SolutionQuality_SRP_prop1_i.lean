-- Prove2me | Theorems.Thm_SolutionQuality_SRP_prop1_i
-- name    : SolutionQuality.SRP.prop1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:18.833178+00:00
-- url     : https://prove2.me/theorems/2fd2355b-92aa-4423-b2db-6cfc35c98d4e
-- title:
--   Proposition 1 (i), p. 6 — z*_n → z*, w.p.1
-- statement:
--   Assume (A1)–(A3), and let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. as $\tilde\xi$. Let $z^*=\min_{x\in X}Ef(x,\tilde\xi)$ be the optimal value of (SP) and $z_n^*=\min_{x\in X}\frac1n\sum_{i=1}^n f(x,\tilde\xi^i)$ the optimal value of the sample average approximation (SP$_n$). Then
--   $$
--   z_n^*\longrightarrow z^*\qquad\text{as } n\to\infty,\ \text{w.p.1}.
--   $$
--
--   The optimal value of the sampled problem is a strongly consistent estimator of the true optimal value; this is part (i) of Proposition 1, used in the proof of part (ii).
--
--   **Formalization Note.** The paper's hypothesis $\hat x\in X$ is not used by this part and is dropped (the statement is stronger without it). $f(x,\cdot)$ is assumed measurable for each $x$. $z^*$ and $z_n^*$ are infima of images of $X$; under (A1)–(A3) they are attained on the probability-one event where the sample objective is continuous.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), p. 6, Proposition 1 (i)

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

theorem prop1_i {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => saaValue f X (fun i => ξ i ω) n) atTop
      (𝓝 (optValue μ f X)) := by sorry

end SolutionQuality.SRP
