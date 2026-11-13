-- Prove2me | Theorems.Thm_TentNoise_lemma_A_3
-- name    : TentNoise.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:35.733185+00:00
-- url     : https://prove2.me/theorems/0fa38967-4789-46fb-b3ea-8f0e6fc2c7dd
-- title:
--   Lemma A.3 — path-space $T_1$ inequality for the noised tent map
-- statement:
--   For every $T\ge1$, every $\sigma\ge0$ and every probability measure $\nu$ on $[0,1]^{T+1}$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\nu,\mathbb P^\sigma_T\bigr)\le\sqrt{\frac{2}{T+1}\,D_{\mathrm{KL}}\bigl(\nu\,\|\,\mathbb P^\sigma_T\bigr)} ,
--   $$
--
--   where $\mathbb P^\sigma_T$ is the noised tent-map path law and $D_{\mathrm{KL}}$ is the Kullback–Leibler divergence.
--
--   This transport–entropy inequality on path space, uniform in the horizon, converts the KL bound between the two noised laws (Lemma A.8) into a Wasserstein bound.
--
--   **Formalization Note** $D_{\mathrm{KL}}$ is Mathlib's `klDiv`, valued in $[0,\infty]$ and equal to $\infty$ off absolute continuity; the square root is taken in $[0,\infty]$, so an infinite divergence gives the trivial bound $\infty$.
--
--   Differences from the source:
--   - encoding: paths in [0,1]^{T+1}, laws on the cube → paths Fin (T+1) → ℝ, laws on ℝ^{T+1} concentrated on the cube; reason: same instances; the coordinates of every path the laws charge lie in [0,1]
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
--   - encoding: √(2/(T+1) · D_KL) with D_KL possibly infinite → (ofReal(2/(T+1)) · klDiv ν ℙ^σ_T)^(1/2) in [0,∞]; reason: Lean convention; equal to the real square root when D_KL < ∞, and the claim is immediate (∞) otherwise, as the paper notes
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.3, p.17 (PDF p.17), eq. (21)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma A.3 (Path-space T₁ inequality for the noised tent map)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.3,
p.17, eq. (21)): for every `T ≥ 1`, `σ ≥ 0` and probability measure `ν` on `[0,1]^{T+1}`,
`W_{1,ρ_{1,T}}(ν, ℙ^σ_T) ≤ √(2/(T+1) · D_KL(ν ‖ ℙ^σ_T))`.

**Formalization Note** `ν` is a probability measure on `ℝ^{T+1}` concentrated on `[0,1]^{T+1}`.
`D_KL` is Mathlib's `klDiv`, valued in `[0, ∞]` (`∞` off absolute continuity); the square root is
taken in `[0, ∞]` (`x ^ (1/2)`), so an infinite divergence gives the trivial bound `∞`. -/
theorem lemma_A_3 (T : ℕ) (hT : 1 ≤ T) (σ : ℝ) (hσ : 0 ≤ σ) (ν : Measure (Fin (T + 1) → ℝ))
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, ∀ t, x t ∈ Icc (0 : ℝ) 1) :
    pathW1 T ν (noisedTentLaw σ T) ≤
      (ENNReal.ofReal (2 / ((T : ℝ) + 1)) * klDiv ν (noisedTentLaw σ T)) ^ (1 / 2 : ℝ) := by sorry

end TentNoise
