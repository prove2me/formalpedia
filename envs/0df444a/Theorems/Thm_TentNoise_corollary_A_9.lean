-- Prove2me | Theorems.Thm_TentNoise_corollary_A_9
-- name    : TentNoise.corollary_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:10.713525+00:00
-- url     : https://prove2.me/theorems/6a207907-4489-4f6a-92d5-f9b267bf566e
-- title:
--   Corollary A.9 — Wasserstein distance between the noised path laws
-- statement:
--   Let $g:[0,1]\to[0,1]$ be Borel, $\sigma>0$ and $T\ge1$. Then
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P^\sigma_T,\mathbb Q^\sigma_T\bigr)\le\sqrt{\frac{T}{T+1}}\,\frac{\sqrt{M_\sigma}\,\varepsilon_P}{\sigma}\le\frac{\sqrt{1+\sqrt{2/\pi}/\sigma}}{\sigma}\,\varepsilon_P .
--   $$
--
--   For $\sigma^2\ge16\,\varepsilon_P$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P^\sigma_T,\mathbb Q^\sigma_T\bigr)\le\sqrt{\frac{2T}{T+1}}\,\frac{\varepsilon_P}{\sigma}\le\sqrt2\,\frac{\varepsilon_P}{\sigma}.
--   $$
--
--   This is the second term of the triangle inequality behind the main upper bound: the cost of replacing $f$ by $g$ when both are noised, uniform in $T$.
--
--   **Formalization Note** $\sqrt{T/(T+1)}\,\sqrt{M_\sigma}$ is computed in $[0,\infty]$ as $\bigl(\tfrac{T}{T+1}M_\sigma\bigr)^{1/2}$ because $M_\sigma$ is a supremum in $[0,\infty]$; the last inequality of the second display is between real numbers.
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] Borel; paths in [0,1]^{T+1} → g : ℝ → ℝ measurable with g([0,1]) ⊆ [0,1]; paths Fin (T+1) → ℝ; reason: every path law is concentrated on [0,1]^{T+1} and values of g off [0,1] are never visited; every Borel map of [0,1] extends to a Borel map of ℝ
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
--   - reading: horizon T unrestricted in the statement → T ≥ 1; reason: the corollary combines (21), stated for T ≥ 1, with (43)/(45), whose ε_Q² needs T ≥ 1
--   - encoding: √(T/(T+1)) √M_σ ε_P/σ, real → ((T/(T+1)) · M_σ)^(1/2) · ofReal(ε_P/σ) in [0,∞]; reason: M_σ is a supremum in [0,∞]; equal to the real expression when M_σ < ∞
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Corollary A.9, p.22 (PDF p.22), eqs. (50)–(51)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP
import Definitions.Def_TentNoise_Msup

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Corollary A.9 (Wasserstein distance of noised distributions)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Corollary A.9,
p.22, eqs. (50)–(51)): for every `σ > 0`,
`W_{1,ρ_{1,T}}(ℙ^σ_T, ℚ^σ_T) ≤ √(T/(T+1)) √M_σ ε_P/σ ≤ (√(1 + √(2/π)/σ)/σ) ε_P`;
and for `σ² ≥ 16 ε_P`, `W_{1,ρ_{1,T}}(ℙ^σ_T, ℚ^σ_T) ≤ √(2T/(T+1)) ε_P/σ ≤ √2 ε_P/σ`.

**Formalization Note** `√(T/(T+1)) √M_σ` is computed in `[0, ∞]` as `((T/(T+1)) · M_σ)^{1/2}`, since
`M_σ` is a supremum in `[0, ∞]`; the last inequality of (51) is between real numbers. `T ≥ 1` (the range
of Lemma A.3 and of `ε_Q²`, from which the corollary is derived). `g` is any Borel map with
`g([0,1]) ⊆ [0,1]`. -/
theorem corollary_A_9 (g : ℝ → ℝ) (hg : Measurable g) (hgI : MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1))
    (σ : ℝ) (hσ : 0 < σ) (T : ℕ) (hT : 1 ≤ T) :
    (pathW1 T (noisedTentLaw σ T) (noisedLaw g hg σ T) ≤
        (ENNReal.ofReal ((T : ℝ) / ((T : ℝ) + 1)) * Msup σ) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (errP g / σ) ∧
      (ENNReal.ofReal ((T : ℝ) / ((T : ℝ) + 1)) * Msup σ) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (errP g / σ) ≤
        ENNReal.ofReal (Real.sqrt (1 + Real.sqrt (2 / Real.pi) / σ) / σ * errP g)) ∧
    (16 * errP g ≤ σ ^ 2 →
      pathW1 T (noisedTentLaw σ T) (noisedLaw g hg σ T) ≤
          ENNReal.ofReal (Real.sqrt (2 * T / ((T : ℝ) + 1)) * (errP g / σ)) ∧
        Real.sqrt (2 * T / ((T : ℝ) + 1)) * (errP g / σ) ≤ Real.sqrt 2 * (errP g / σ)) := by sorry

end TentNoise
