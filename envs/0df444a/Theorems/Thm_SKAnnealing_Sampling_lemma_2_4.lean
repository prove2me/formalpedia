-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_2_4
-- name    : SKAnnealing.Sampling.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:29.339184+00:00
-- url     : https://prove2.me/theorems/8becf66f-fdb4-4f01-8c65-01e07b68e587
-- title:
--   Lemma 2.4, p. 11 — localization criterion: path covariance $\le K$ and end-point Poincaré $\rho_T$ give a $(\rho_Te^{KT},C\delta e^{KT})$-weak Poincaré inequality
-- statement:
--   Let $\mu$ be a fixed probability distribution on $\{\pm1\}^N$. Let $\sigma\sim\mu$ and let $(B_t)_{t\ge0}$ be an independent standard Brownian motion in $\mathbb R^N$. **Stochastic localization** initialized at $\mu$ is the measure-valued process
--   $$\mu_t(y)\propto\mu(y)\,\exp\langle t\sigma+B_t,\,y\rangle,\qquad t\ge0 .$$
--
--   **Lemma 2.4 (Localization criterion).** There is a universal constant $C>0$ with the following property. Let $T\ge0$, $K\ge0$, $\rho_T>0$ and $\delta\ge0$, and suppose that, with probability at least $1-\delta$, both
--   1. $\sup_{0\le t\le T}\|\mathbf{Cov}(\mu_t)\|_{\mathrm{op}}\le K$, and
--   2. $\mu_T$ satisfies a Poincaré inequality with constant $\rho_T$.
--
--   Then $\mu$ satisfies a $(\rho_Te^{KT},\,C\delta e^{KT})$-weak Poincaré inequality.
--
--   This is the bridge from covariance control along the localization path (display (7)) and the end-point Poincaré inequality (Lemma 1.5) to the weak Poincaré inequality of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: stochastic localization (3) started at µ → µ_t = tilt(µ, tσ + B_t) with σ ∼ µ independent of a standard Brownian motion B in ℝ^N, on any probability space carrying them; reason: this is the posterior representation the paper itself uses ([EM22], p. 3), equal in law to (3) (reading R6)
--   - encoding: with probability at least 1 − δ, the two events hold → the (outer) probability that the two events do not both hold is ≤ δ; reason: a bound on the bad set; the event involves uncountably many times, so it is not assumed measurable
--   - encoding: K (a bound on an operator norm) → K ≥ 0, ρ_T > 0, δ ≥ 0; reason: K bounds a norm, ρ_T is a Poincaré constant and δ a probability; for δ < 1 the hypothesis already forces K ≥ 0, and K < 0 with δ ≥ 1 is a degenerate case outside the lemma
--   - reading: C → one universal constant C > 0; reason: C is printed as a constant of the criterion, independent of µ, N, T, K, ρ_T and δ
--   - reading: the standard Dirichlet form ℰ(f, f) and ‖f‖_∞ in display (2) → ℰ(f, f) = N^{−1} Σ_i E_µ[(f − P_i f)²] (the discrete Glauber chain of Definition 2.1), ‖f‖_∞ the maximum of |f| on the support of µ; reason: the (O(N), ·) constants fit the discrete-time chain; on the full-support Gibbs laws of the paper the support is all of {±1}^N (reading R7)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 2.4, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_IsWeakPoincare
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_IsStdBrownian

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 2.4** (localization criterion). Let `(µ_t)_{0 ≤ t ≤ T}` be stochastic localization initialized at a
fixed distribution `µ` on `{±1}^N`. Suppose that, with probability at least `1 − δ`, `sup_{0 ≤ t ≤ T} ‖Cov(µ_t)‖_op ≤ K`
and `µ_T` satisfies a Poincaré inequality with constant `ρ_T`. Then `µ` satisfies a `(ρ_T e^{KT}, C δ e^{KT})`-weak
Poincaré inequality.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 2.4, p. 11 (PDF p. 13).

**Formalization Note** Reading R6: `µ_t = tilt µ (t σ + B_t)` with `σ ∼ µ` independent of a standard Brownian motion
`B` in `ℝ^N`, on any probability space. `C > 0` is universal. "With probability at least `1 − δ`" is the bad-set
bound `P(bad) ≤ δ`. `0 ≤ K` (encoding: `K` bounds a norm), `ρ_T > 0`, `δ ≥ 0`. -/
theorem lemma_2_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (μ : Spin N → ℝ), (∀ x, 0 ≤ μ x) → ∑ x, μ x = 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (σ : Ω → Spin N) (B : ℝ≥0 → Ω → (Fin N → ℝ)),
        Measurable σ → (∀ x, P (σ ⁻¹' {x}) = ENNReal.ofReal (μ x)) → IsStdBrownian B P →
        IndepFun σ (fun ω t => B t ω) P →
        ∀ (T : ℝ≥0) (K ρT δ : ℝ), 0 ≤ K → 0 < ρT → 0 ≤ δ →
          P {ω | ¬ ((∀ t : ℝ≥0, t ≤ T →
                lawCovNorm (tilt μ ((t : ℝ) • spinVec (σ ω) + B t ω)) ≤ K) ∧
              IsPoincare (tilt μ ((T : ℝ) • spinVec (σ ω) + B T ω)) ρT)} ≤ ENNReal.ofReal δ →
          IsWeakPoincare μ (ρT * Real.exp (K * T)) (C * δ * Real.exp (K * T)) := by sorry

end SKAnnealing.Sampling
