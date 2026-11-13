-- Prove2me | Theorems.Thm_TentNoise_lemma_A_2
-- name    : TentNoise.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:00.779286+00:00
-- url     : https://prove2.me/theorems/caf9d936-52a1-429c-8c64-8ef5df37a349
-- title:
--   Lemma A.2 — horizon-uniform noising bias: $W_{1,\rho_{1,T}}(\mathbb P_T,\mathbb P^\sigma_T)\le\sqrt{2/\pi}\,\sigma$
-- statement:
--   Let $\mathbb P_T$ be the path law of the tent map from $X_0\sim\mu$ and $\mathbb P^\sigma_T$ the path law of the noised tent map ($X_{t+1}\sim H_\sigma(f(X_t),\cdot)$), with $\sigma\ge0$. For every $T\ge1$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb P^\sigma_T\bigr)\le\sqrt{\tfrac2\pi}\,\sigma .
--   $$
--
--   The bias introduced by noising the true dynamics is thus bounded independently of the horizon; it is the first term of the triangle inequality behind the main upper bound.
--
--   Differences from the source:
--   - encoding: paths in [0,1]^{T+1}, laws on the cube → paths Fin (T+1) → ℝ, laws on ℝ^{T+1} concentrated on the cube; reason: same instances; the coordinates of every path the laws charge lie in [0,1]
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.2, p.16 (PDF p.16), eq. (19)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma A.2 (Horizon-uniform Gaussian noising bias bound)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.2, p.16,
eq. (19)): for every `T ≥ 1`, `W_{1,ρ_{1,T}}(ℙ_T, ℙ^σ_T) ≤ √(2/π) σ`.

**Formalization Note** `σ ≥ 0` (the kernel's noise levels; `σ` is a standard deviation). -/
theorem lemma_A_2 (T : ℕ) (hT : 1 ≤ T) (σ : ℝ) (hσ : 0 ≤ σ) :
    pathW1 T (trueLaw T) (noisedTentLaw σ T) ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * σ) := by sorry

end TentNoise
