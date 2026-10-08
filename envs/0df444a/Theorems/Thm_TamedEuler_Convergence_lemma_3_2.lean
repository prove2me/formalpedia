-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_2
-- name    : TamedEuler.Convergence.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:13.234154+00:00
-- url     : https://prove2.me/theorems/2331ac1a-66e8-473a-bd1b-d2af6d02ee64
-- title:
--   Lemma 3.2, p. 15 — 𝔼[exp(a‖Z‖²)] = (1−2a)^{−n/2} ≤ e^{2an} for a standard normal Z and a ∈ [0, 1/4]
-- statement:
--   Let $n\in\mathbb N=\{1,2,\dots\}$ and let $Z:\Omega\to\mathbb R^n$ be an $n$-dimensional standard normal random vector on a probability space $(\Omega,\mathcal F,\mathbb P)$. Then
--   $$\mathbb E\big[\exp(a\|Z\|^2)\big]=(1-2a)^{-n/2}\le e^{2an}$$
--   for all $a\in[0,\tfrac14]$.
--
--   This exponential moment of a chi-squared variable is used to bound the exponential moments of $\sum_k\|\Delta W^N_k\|^2$ (Lemma 3.3).
--
--   **Formalization Note** "Standard normal" is `HasLaw Z (stdGaussian ℝⁿ) ℙ`. The expectation is the integral of the nonnegative function $\exp(a\|Z\|^2)$ with values in $[0,\infty]$, so the equality includes finiteness.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.2, (28)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence


/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 15, Lemma 3.2, (28): for
`n ∈ ℕ` and an `n`-dimensional standard normal random vector `Z`,
`𝔼[exp(a ‖Z‖²)] = (1 − 2a)^{−n/2} ≤ e^{2an}` for all `a ∈ [0, 1/4]`. The expectation is a
`[0, ∞]`-valued integral. -/
theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin n))) P) :
    ∀ a : ℝ, a ∈ Set.Icc (0 : ℝ) (1 / 4) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * ‖Z ω‖ ^ 2)) ∂P
          = ENNReal.ofReal ((1 - 2 * a) ^ (-(n : ℝ) / 2)) ∧
        (1 - 2 * a) ^ (-(n : ℝ) / 2) ≤ Real.exp (2 * a * n) := by sorry

end TamedEuler.Convergence
