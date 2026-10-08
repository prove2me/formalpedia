-- Prove2me | Theorems.Thm_SolutionQuality_SRP_fbar_tendstoUniformlyOn
-- name    : SolutionQuality.SRP.fbar_tendstoUniformlyOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:48:05.610329+00:00
-- url     : https://prove2.me/theorems/d8302458-b8f8-4543-a622-cb5de0f59b37
-- title:
--   Proof of Proposition 1, p. 6 — f̄_n(x) → Ef(x, ξ̃) uniformly on X, w.p.1
-- statement:
--   Assume (A1)–(A3), and let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. as $\tilde\xi$. Then, with probability one, the sample mean functions $\bar f_n(x)=\frac1n\sum_{i=1}^n f(x,\tilde\xi^i)$ converge to the expected cost $Ef(x,\tilde\xi)$ uniformly on $X$:
--   $$
--   \sup_{x\in X}\big|\bar f_n(x)-Ef(x,\tilde\xi)\big|\xrightarrow[n\to\infty]{}0\qquad\text{w.p.1}.
--   $$
--
--   This uniform strong law of large numbers is the engine behind every consistency statement of the paper: it yields convergence of optimal values (Proposition 1 (i)) and of optimal solutions (Proposition 1 (ii)). The paper quotes it from Rubinstein and Shapiro, Lemma A1.
--
--   **Formalization Note.** The candidate $\hat x$ and the minimizers $x_n^*$ play no role and are not hypotheses. $f(x,\cdot)$ is assumed measurable for each $x$ (the paper's "$f(x,\tilde\xi)$ is a random variable"). Uniform convergence on $X$ is Mathlib's `TendstoUniformlyOn`.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), p. 6, proof of Proposition 1, second sentence

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

theorem fbar_tendstoUniformlyOn {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n x => sampleMean f (fun i => ξ i ω) n x)
      (expectedCost μ f) atTop X := by sorry

end SolutionQuality.SRP
