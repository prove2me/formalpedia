-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_laplace_identity
-- name    : RogersSatchell.Unbiased.laplace_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:25.899648+00:00
-- url     : https://prove2.me/theorems/f695b1e6-ff6c-45b6-b0cb-10154a0451ff
-- title:
--   Section 2, p. 505 — E S_T(S_T − X_T) = ∫₀^∞ λe^{−λt} E S_t(S_t − X_t) dt
-- statement:
--   Let $B$ be a standard Brownian motion with every sample path continuous, $c\in\mathbb R$, $\sigma\ge0$, $X_t=\sigma B_t+ct$, with running maximum $S_t$ over $[0,t]$, and write $g(t)=E[S_t(S_t-X_t)]$. Let $T$ be exponential with rate $\lambda>0$, independent of the path $B$. Then $S_T(S_T-X_T)$ is integrable, $t\mapsto\lambda e^{-\lambda t}g(t)$ is integrable on $(0,\infty)$, and
--   $$E\big[S_T(S_T-X_T)\big]=\int_0^\infty \lambda e^{-\lambda t}\,E\big[S_t(S_t-X_t)\big]\,dt.$$
--
--   This expresses the exponential-time expectation as $\lambda$ times the Laplace transform of $g$ at $\lambda$; combined with the value $\sigma^2/2\lambda$, it determines $g$.
--
--   **Formalization Note** The paper writes $\int_0^\infty\lambda e^{-\lambda t}\,dt\,ES_t(S_t-X_t)$; the integrability of both sides is made explicit. The identity uses only the independence of $T$ and $B$, so it is stated for $\sigma\ge0$. The fixed-time expectation $g(t)$ is a Bochner integral evaluated at time $t\in(0,\infty)$.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 505: `E S_T(S_T − X_T) = ∫₀^∞ λ e^{−λt} E S_t(S_t − X_t) dt` for an
exponential time `T` of rate `λ` independent of `B`. -/
theorem laplace_identity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ)
    (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hT : HasLaw T (expMeasure lam) P)
    (hTB : IndepFun T (fun ω => fun t => B t ω) P) :
    Integrable (fun ω => runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω)) P ∧
    IntegrableOn (fun t : ℝ => lam * Real.exp (-(lam * t)) *
      ∫ ω, runMax σ c B t.toNNReal ω * (runMax σ c B t.toNNReal ω - logPrice σ c B t.toNNReal ω) ∂P)
      (Set.Ioi 0) ∧
    ∫ ω, runMax σ c B (T ω).toNNReal ω *
      (runMax σ c B (T ω).toNNReal ω - logPrice σ c B (T ω).toNNReal ω) ∂P
      = ∫ t in Set.Ioi (0 : ℝ), lam * Real.exp (-(lam * t)) *
          ∫ ω, runMax σ c B t.toNNReal ω *
            (runMax σ c B t.toNNReal ω - logPrice σ c B t.toNNReal ω) ∂P := by sorry

end RogersSatchell.Unbiased
