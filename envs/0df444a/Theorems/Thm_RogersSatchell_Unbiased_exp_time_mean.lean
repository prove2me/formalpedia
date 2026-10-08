-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_exp_time_mean
-- name    : RogersSatchell.Unbiased.exp_time_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:50.691854+00:00
-- url     : https://prove2.me/theorems/4ce89f27-1a04-496b-84e2-43abc1b631ba
-- title:
--   Section 2, p. 505 — E S_T(S_T − X_T) = 1/(αβ) = σ²/2λ at an independent exponential time
-- statement:
--   Let $B$ be a standard Brownian motion with every sample path continuous, $c\in\mathbb R$, $\sigma>0$, $X_t=\sigma B_t+ct$, with running maximum $S_t$ over $[0,t]$. Let $T$ be exponential with rate $\lambda>0$, independent of the path $B$, and let $\alpha,\beta$ be as in the definition file. Then $S_T(S_T-X_T)$ is integrable and
--   $$E\big[S_T(S_T-X_T)\big]=\frac{1}{\alpha\beta}=\frac{\sigma^2}{2\lambda}.$$
--
--   The value does not depend on the drift $c$; this is the exponential-time form of the key identity of the paper.
--
--   **Formalization Note** The expectation is a Bochner integral, and integrability is asserted explicitly so that the identity cannot hold by Lean's convention that the integral of a non-integrable function is $0$. Both equalities of the page's final two lines are stated.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 505: `E S_T(S_T − X_T) = 1/(αβ) = σ²/2λ` at an independent exponential
time `T` of rate `λ`. -/
theorem exp_time_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ)
    (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hT : HasLaw T (expMeasure lam) P)
    (hTB : IndepFun T (fun ω => fun t => B t ω) P) :
    Integrable (fun ω => runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω)) P ∧
    ∫ ω, runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) ∂P
      = 1 / (alpha σ c lam * beta σ c lam) ∧
    ∫ ω, runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) ∂P
      = σ ^ 2 / (2 * lam) := by sorry

end RogersSatchell.Unbiased
