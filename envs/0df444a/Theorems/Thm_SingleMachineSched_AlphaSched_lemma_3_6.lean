-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_lemma_3_6
-- name    : SingleMachineSched.AlphaSched.lemma_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:14:18.657732+00:00
-- url     : https://prove2.me/theorems/b789b627-1791-4fcb-94ae-8253e3ed538e
-- title:
--   Lemma 3.6 — the truncated exponential density and its two integral bounds
-- statement:
--   Let $0 < \gamma < 1$ satisfy
--
--   $$1 - \frac{\gamma^2}{1 + \gamma} = \gamma + \ln(1 + \gamma),$$
--
--   and let $c = \frac{1+\gamma}{1+\gamma-e^{-\gamma}}$, $\delta = 1 - \frac{\gamma^2}{1+\gamma}$ and $f(\alpha) = (c-1)e^\alpha$ for $0 < \alpha \le \delta$, $f(\alpha) = 0$ otherwise. Then $f$ is a density function on $[0,1]$: $f \ge 0$ everywhere and $\int_0^1 f(\alpha)\, d\alpha = 1$. Moreover:
--
--   1. for all $\eta \in [0, 1]$,
--   $$\int_0^\eta f(\alpha)(1 + \alpha - \eta)\, d\alpha \le (c - 1)\, \eta ;$$
--   2. for all $\mu \in [0, 1]$,
--   $$\int_\mu^1 f(\alpha)(1 + \alpha)\, d\alpha \le c\, (1 - \mu).$$
--
--   Property 1 controls the delay of a job caused by jobs of $N_1$, property 2 the delay caused by jobs of $N_2$, in the bound (3.11).
--
--   **Formalization Note** The integrals are interval integrals of a bounded, piecewise continuous function, so they are ordinary Lebesgue integrals.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 183, Lemma 3.6

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_Density

namespace SingleMachineSched.AlphaSched

/-- Lemma 3.6 (Goemans et al. 2002, p. 183): for `γ ∈ (0, 1)` solving
`1 - γ²/(1+γ) = γ + ln(1+γ)`, the function `f` of Theorem 3.5 is a density function on `[0, 1]`
with (i) `∫_0^η f(α)(1 + α - η) dα ≤ (c - 1) η` for all `η ∈ [0, 1]` and
(ii) `∫_μ^1 f(α)(1 + α) dα ≤ c (1 - μ)` for all `μ ∈ [0, 1]`. -/
theorem lemma_3_6 (γ : ℝ)
    (hγ : 0 < γ ∧ γ < 1 ∧ 1 - γ ^ 2 / (1 + γ) = γ + Real.log (1 + γ)) :
    ((∀ a, 0 ≤ fDens γ a) ∧ ∫ a in (0 : ℝ)..1, fDens γ a = 1) ∧
      (∀ η ∈ Set.Icc (0 : ℝ) 1,
        ∫ a in (0 : ℝ)..η, fDens γ a * (1 + a - η) ≤ (cConst γ - 1) * η) ∧
      (∀ μ ∈ Set.Icc (0 : ℝ) 1,
        ∫ a in μ..1, fDens γ a * (1 + a) ≤ cConst γ * (1 - μ)) := by sorry

end SingleMachineSched.AlphaSched
