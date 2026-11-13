-- Prove2me | Theorems.Thm_TentNoise_theorem_A_10
-- name    : TentNoise.theorem_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:00.553168+00:00
-- url     : https://prove2.me/theorems/93ac20a6-7c09-46a6-bf2f-2897ba7a35a0
-- title:
--   Theorem A.10 — main upper bound: $W_{1,\rho_{1,T}}(\mathbb P_T,\mathbb Q^{\sigma^*}_T)\le4\sqrt{\varepsilon_P}$ at $\sigma^*=4\sqrt{\varepsilon_P}$
-- statement:
--   Let $g:[0,1]\to[0,1]$ be Borel with one-step error $\varepsilon_P=\|f-g\|_{L^2(\mu)}$. For every $T\ge1$ and every $\sigma>0$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb Q^\sigma_T\bigr)\le\frac{\sqrt{1+\sqrt{2/\pi}/\sigma}}{\sigma}\,\varepsilon_P+\sqrt{\tfrac2\pi}\,\sigma .
--   $$
--
--   Whenever $\sigma^2\ge16\,\varepsilon_P$, the sharper estimate
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb Q^\sigma_T\bigr)\le\sqrt2\,\frac{\varepsilon_P}{\sigma}+\sqrt{\tfrac2\pi}\,\sigma
--   $$
--
--   holds for every $T\ge1$. In particular, with $\sigma^*=4\sqrt{\varepsilon_P}$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb Q^{\sigma^*}_T\bigr)\le4\sqrt{\varepsilon_P}\qquad\text{uniformly in }T\ge1 .
--   $$
--
--   Only one-step accuracy of $g$ is assumed, yet the whole trajectory law of the noised rollout is accurate at every horizon.
--
--   **Formalization Note** The last clause covers $\varepsilon_P=0$, where $\sigma^*=0$ and the rollout is deterministic.
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] Borel; paths in [0,1]^{T+1} → g : ℝ → ℝ measurable with g([0,1]) ⊆ [0,1]; paths Fin (T+1) → ℝ; reason: every path law is concentrated on [0,1]^{T+1} and values of g off [0,1] are never visited; every Borel map of [0,1] extends to a Borel map of ℝ
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
--   - generalization: (55) at σ* = 4√ε_P inside 'for every σ > 0' (the proof: 'for ε_P > 0') → the last conjunct holds for every g, including ε_P = 0 (σ* = 0, the deterministic rollout ℚ^g_T); reason: it specializes to the source's claim for every ε_P > 0; at ε_P = 0, g = f µ-a.e. and f preserves µ, so ℚ^{g,0}_T = ℙ_T and the bound reads 0 ≤ 0 (Theorem 3.1's (11) states it without the restriction)
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Theorem A.10, p.23 (PDF p.23), eqs. (52)–(55)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Theorem A.10 (Main, `W_{1,ρ_{1,T}}` distance)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Theorem A.10, p.23,
eqs. (52)–(55)): for every `T ≥ 1` and every `σ > 0`,
`W_{1,ρ_{1,T}}(ℙ_T, ℚ^σ_T) ≤ (√(1 + √(2/π)/σ)/σ) ε_P + √(2/π) σ`; whenever `σ² ≥ 16 ε_P`,
`W_{1,ρ_{1,T}}(ℙ_T, ℚ^σ_T) ≤ √2 ε_P/σ + √(2/π) σ` for every `T ≥ 1`; and with `σ* = 4√ε_P`,
`W_{1,ρ_{1,T}}(ℙ_T, ℚ^{σ*}_T) ≤ 4√ε_P`, uniformly in `T`.

**Formalization Note** `g` is any Borel map with `g([0,1]) ⊆ [0,1]`; no other hypothesis. The last
clause includes `ε_P = 0` (then `σ* = 0`, the deterministic rollout). -/
theorem theorem_A_10 (g : ℝ → ℝ) (hg : Measurable g) (hgI : MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1)) :
    (∀ T : ℕ, 1 ≤ T → ∀ σ : ℝ, 0 < σ →
      pathW1 T (trueLaw T) (noisedLaw g hg σ T) ≤
          ENNReal.ofReal (Real.sqrt (1 + Real.sqrt (2 / Real.pi) / σ) / σ * errP g +
            Real.sqrt (2 / Real.pi) * σ) ∧
        (16 * errP g ≤ σ ^ 2 →
          pathW1 T (trueLaw T) (noisedLaw g hg σ T) ≤
            ENNReal.ofReal (Real.sqrt 2 * (errP g / σ) + Real.sqrt (2 / Real.pi) * σ))) ∧
    (∀ T : ℕ, 1 ≤ T →
      pathW1 T (trueLaw T) (noisedLaw g hg (4 * Real.sqrt (errP g)) T) ≤
        ENNReal.ofReal (4 * Real.sqrt (errP g))) := by sorry

end TentNoise
