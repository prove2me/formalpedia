-- Prove2me | Theorems.Thm_TentNoise_corollary_A_7
-- name    : TentNoise.corollary_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:08.96131+00:00
-- url     : https://prove2.me/theorems/43409277-97b5-4c2c-9eff-fd9d7848b57b
-- title:
--   Corollary A.7 — transfer of error to the noised rollout
-- statement:
--   Let $g:[0,1]\to[0,1]$ be Borel and $\sigma>0$, and let $(Y_0,\dots,Y_T)\sim\mathbb Q^\sigma_T$. For every $t\in\{0,\dots,T\}$,
--
--   $$
--   \mathbb E_{\mathbb Q^\sigma_T}|f(Y_t)-g(Y_t)|^2\le M_\sigma\,\varepsilon_P^2 ,
--   $$
--
--   and if moreover $\sigma^2\ge16\,\varepsilon_P$,
--
--   $$
--   \mathbb E_{\mathbb Q^\sigma_T}|f(Y_t)-g(Y_t)|^2\le2\,\varepsilon_P^2 .
--   $$
--
--   The one-step error of $g$ measured along the noised rollout is thus at most a constant multiple of its error under the stationary law.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of the nonnegative integrand, in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] Borel; paths in [0,1]^{T+1} → g : ℝ → ℝ measurable with g([0,1]) ⊆ [0,1]; paths Fin (T+1) → ℝ; reason: every path law is concentrated on [0,1]^{T+1} and values of g off [0,1] are never visited; every Borel map of [0,1] extends to a Borel map of ℝ
--   - encoding: E_{ℚ^σ_T}|f(Y_t) − g(Y_t)|², real → lower Lebesgue integral in [0,∞]; right sides through ENNReal.ofReal; reason: nonnegative integrand; same value, and no integrability side condition
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Corollary A.7, p.21 (PDF p.21)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP
import Definitions.Def_TentNoise_Msup

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Corollary A.7 (Transfer of error)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Corollary A.7, p.21): for `σ > 0`,
`E_{ℚ^σ_T} |f(Y_t) − g(Y_t)|² ≤ M_σ ε_P²` for `t ≥ 0`; and if `σ² ≥ 16 ε_P`,
`E_{ℚ^σ_T} |f(Y_t) − g(Y_t)|² ≤ 2 ε_P²` for `t ≥ 0`.

**Formalization Note** `t` ranges over the times `0, …, T` of the path. The expectation is the lower
Lebesgue integral of the nonnegative integrand, in `[0, ∞]`. `g` is any Borel map with
`g([0,1]) ⊆ [0,1]`. -/
theorem corollary_A_7 (g : ℝ → ℝ) (hg : Measurable g) (hgI : MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1))
    (σ : ℝ) (hσ : 0 < σ) (T : ℕ) (t : Fin (T + 1)) :
    ∫⁻ p, ENNReal.ofReal ((tentMap 2 (p t) - g (p t)) ^ 2) ∂(noisedLaw g hg σ T) ≤
        Msup σ * ENNReal.ofReal (errP g ^ 2) ∧
    (16 * errP g ≤ σ ^ 2 →
      ∫⁻ p, ENNReal.ofReal ((tentMap 2 (p t) - g (p t)) ^ 2) ∂(noisedLaw g hg σ T) ≤
        ENNReal.ofReal (2 * errP g ^ 2)) := by sorry

end TentNoise
