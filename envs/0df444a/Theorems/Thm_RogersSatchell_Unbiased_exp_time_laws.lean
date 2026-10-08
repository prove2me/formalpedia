-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_exp_time_laws
-- name    : RogersSatchell.Unbiased.exp_time_laws
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:36.035548+00:00
-- url     : https://prove2.me/theorems/75f15bf9-8e36-46ca-9220-2807e93261b2
-- title:
--   Section 2, p. 505 — at an independent exponential time T of rate λ, S_T ~ Exp(α) and −I_T ~ Exp(β)
-- statement:
--   Let $B$ be a standard Brownian motion on a probability space $(\Omega,\mathcal F,P)$ with every sample path continuous, let $c\in\mathbb R$ and $\sigma>0$, and let $X_t=\sigma B_t+ct$ with running maximum $S_t$ and running minimum $I_t$ over $[0,t]$. Let $\lambda>0$ and let $T$ be an exponential random variable with mean $\lambda^{-1}$ (rate $\lambda$), independent of the whole path $B$. Then
--   $$S_T\sim\operatorname{Exp}(\alpha),\qquad -I_T\sim\operatorname{Exp}(\beta),$$
--   where $\operatorname{Exp}(r)$ is the exponential law with density $re^{-rx}$ on $x\ge 0$ and
--   $$\alpha=\frac{\sqrt{c^2+2\lambda\sigma^2}-c}{\sigma^2},\qquad \beta=\frac{\sqrt{c^2+2\lambda\sigma^2}+c}{\sigma^2}.$$
--
--   Together with the Wiener–Hopf splitting, this gives the explicit joint law at an exponential time from which every moment computation of the paper follows.
--
--   **Formalization Note** "Exponential with parameter $\alpha$" is read as rate $\alpha$ (mean $1/\alpha$), matching the paper's later use $ES_T=1/\alpha$; Mathlib's `expMeasure r` has density $re^{-rx}$. "Independent of $B$" is independence of $T$ from the path-valued random variable $\omega\mapsto(t\mapsto B_t(\omega))$ with the product σ-algebra, not from each $B_t$ separately. $S_T$ is evaluated at $T(\omega)$ truncated to $[0,\infty)$, which changes nothing since $T\ge0$ almost surely. `HasLaw` includes almost-everywhere measurability. $\sigma>0$ is required because $\alpha,\beta$ divide by $\sigma^2$.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 505: if `T` is exponential with mean `λ⁻¹` and independent of the
Brownian motion `B`, then `S_T` is exponential with rate `α` and `−I_T` is exponential with rate
`β`. Requires `σ > 0` (α, β divide by `σ²`). -/
theorem exp_time_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ)
    (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hT : HasLaw T (expMeasure lam) P)
    (hTB : IndepFun T (fun ω => fun t => B t ω) P) :
    HasLaw (fun ω => runMax σ c B (T ω).toNNReal ω) (expMeasure (alpha σ c lam)) P ∧
    HasLaw (fun ω => - runMin σ c B (T ω).toNNReal ω) (expMeasure (beta σ c lam)) P := by sorry

end RogersSatchell.Unbiased
