-- Prove2me | Theorems.Thm_TentNoise_lemma_A_5
-- name    : TentNoise.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:12.654198+00:00
-- url     : https://prove2.me/theorems/d8289b4c-ac3f-4271-9015-a6535b2bd460
-- title:
--   Lemma A.5 — reflected Gaussian kernel density bound $M_\sigma\le1+\sqrt{2/\pi}/\sigma$
-- statement:
--   Let $\sigma>0$. The reflected Gaussian kernel has a density $h_\sigma(a,y)$ with respect to $\mu$, namely $H_\sigma(a,dy)=h_\sigma(a,y)\,\mu(dy)$ for $a\in[0,1]$, and its supremum $M_\sigma:=\sup_{a,y\in[0,1]}h_\sigma(a,y)$ satisfies
--
--   $$
--   M_\sigma\le1+\frac{\sqrt{2/\pi}}{\sigma}.
--   $$
--
--   This coarse bound holds for all positive noise levels and controls the density of every time marginal of the noised fitted chain.
--
--   **Formalization Note** $h_\sigma$ is the continuous version of the density given by the method of images (equal to the spectral series (29)); the statement asserts that it is a density of $H_\sigma(a,\cdot)$ and bounds its supremum, taken in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: 'Suppose that the reflected Gaussian kernel has density h_σ(a, y) … let M_σ := sup h_σ' → h_σ is the explicit continuous density (method of images, = (29)); that it is a density of H_σ(a, ·) is a conclusion, and M_σ is its supremum; reason: a supremum of a density depends on the version chosen; the paper's proof uses the continuous version (29), which is the one fixed here
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.5, p.18 (PDF p.18), eq. (28)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_H
import Definitions.Def_TentNoise_unifI
import Definitions.Def_TentNoise_Msup

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma A.5 (Reflected Gaussian kernel density bound)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.5, p.18, eq. (28)):
for `σ > 0` the reflected Gaussian kernel has density `h_σ(a, y)` with respect to `µ`,
`H_σ(a, dy) = h_σ(a, y) µ(dy)`, and `M_σ := sup_{a,y∈[0,1]} h_σ(a, y) ≤ 1 + √(2/π)/σ`.

**Formalization Note** `h_σ = reflHeatDensity σ` is the continuous version of the density (the
method-of-images sum, equal to the spectral series (29)); the first conjunct asserts that it is a
density of `H_σ(a, ·)` for every `a ∈ [0, 1]`. `M_σ` is a supremum in `[0, ∞]`. -/
theorem lemma_A_5 (σ : ℝ) (hσ : 0 < σ) :
    (∀ a ∈ Icc (0 : ℝ) 1, H σ a = unifI.withDensity (reflHeatDensity σ a)) ∧
    Msup σ ≤ ENNReal.ofReal (1 + Real.sqrt (2 / Real.pi) / σ) := by sorry

end TentNoise
