-- Prove2me | Theorems.Thm_TentNoise_lemma_A_8
-- name    : TentNoise.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:46:29.569488+00:00
-- url     : https://prove2.me/theorems/178ee6c1-5ad0-4997-a472-107ede4bc699
-- title:
--   Lemma A.8 — KL divergence between the noised path laws
-- statement:
--   Let $g:[0,1]\to[0,1]$ be Borel, $\sigma>0$ and $T\ge1$. Then
--
--   $$
--   D_{\mathrm{KL}}\bigl(\mathbb Q^\sigma_T\,\|\,\mathbb P^\sigma_T\bigr)\le\frac{T\varepsilon_Q^2}{2\sigma^2}\le\frac{TM_\sigma\varepsilon_P^2}{2\sigma^2},
--   $$
--
--   where $M_\sigma\le1+\sqrt{2/\pi}/\sigma$ is as in Lemma A.5. Moreover, if $\sigma^2\ge16\,\varepsilon_P$, then
--
--   $$
--   D_{\mathrm{KL}}\bigl(\mathbb Q^\sigma_T\,\|\,\mathbb P^\sigma_T\bigr)\le\frac{T\varepsilon_P^2}{\sigma^2}.
--   $$
--
--   Here $\varepsilon_Q^2$ is the rollout error of eq. (10). Gaussian smoothing makes the two noised laws mutually comparable in relative entropy, with a cost linear in $T$ that the $1/(T+1)$ of Lemma A.3 cancels.
--
--   **Formalization Note** All quantities are in $[0,\infty]$ (`klDiv`, the rollout error, $M_\sigma$); real constants enter through `ENNReal.ofReal`.
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] Borel; paths in [0,1]^{T+1} → g : ℝ → ℝ measurable with g([0,1]) ⊆ [0,1]; paths Fin (T+1) → ℝ; reason: every path law is concentrated on [0,1]^{T+1} and values of g off [0,1] are never visited; every Borel map of [0,1] extends to a Borel map of ℝ
--   - reading: horizon T unrestricted in the statement → T ≥ 1; reason: ε_Q² (10) divides by T, so the lemma is about T ≥ 1, the range of every horizon statement of the paper
--   - encoding: real-valued KL and error terms → klDiv, errQsq and M_σ in [0,∞]; real constants via ENNReal.ofReal; reason: Lean convention; same values whenever finite
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.8, pp.21–22 (PDF pp.21–22), eqs. (43)–(45)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP
import Definitions.Def_TentNoise_errQsq
import Definitions.Def_TentNoise_Msup

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma A.8 (KL divergence between noised distributions)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.8, pp.21–22,
eqs. (43)–(45)): for every `σ > 0`,
`D_KL(ℚ^σ_T ‖ ℙ^σ_T) ≤ T ε_Q²/(2σ²) ≤ T M_σ ε_P²/(2σ²)`, where `M_σ ≤ 1 + √(2/π)/σ` is as in
Lemma A.5; moreover, if `σ² ≥ 16 ε_P`, then `D_KL(ℚ^σ_T ‖ ℙ^σ_T) ≤ T ε_P²/σ²`.

**Formalization Note** All quantities are in `[0, ∞]` (`klDiv`, `errQsq`, `Msup`); the real constants
enter through `ENNReal.ofReal`. `T ≥ 1`, the range on which `ε_Q²` (10) is defined. `g` is any Borel
map with `g([0,1]) ⊆ [0,1]`. -/
theorem lemma_A_8 (g : ℝ → ℝ) (hg : Measurable g) (hgI : MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1))
    (σ : ℝ) (hσ : 0 < σ) (T : ℕ) (hT : 1 ≤ T) :
    klDiv (noisedLaw g hg σ T) (noisedTentLaw σ T) ≤
        (T : ℝ≥0∞) * errQsq g hg σ T / ENNReal.ofReal (2 * σ ^ 2) ∧
    (T : ℝ≥0∞) * errQsq g hg σ T / ENNReal.ofReal (2 * σ ^ 2) ≤
        (T : ℝ≥0∞) * Msup σ * ENNReal.ofReal (errP g ^ 2) / ENNReal.ofReal (2 * σ ^ 2) ∧
    Msup σ ≤ ENNReal.ofReal (1 + Real.sqrt (2 / Real.pi) / σ) ∧
    (16 * errP g ≤ σ ^ 2 →
      klDiv (noisedLaw g hg σ T) (noisedTentLaw σ T) ≤
        ENNReal.ofReal ((T : ℝ) * errP g ^ 2 / σ ^ 2)) := by sorry

end TentNoise
