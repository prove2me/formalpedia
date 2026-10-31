-- Prove2me | Theorems.Thm_SpiderDiameter_lemma_3_2
-- name    : SpiderDiameter.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:46.436851+00:00
-- url     : https://prove2.me/theorems/61c00923-245a-45ff-9676-0c0f4cdfa67a
-- title:
--   Lemma 3.2: law of $Z_\sigma$ at the first time $Y$ reaches $1/2$
-- statement:
--   Let $n\ge3$ and $(x,y,z)\in\mathcal D$ with $y<\tfrac12$, and let $\sigma=\inf\{t>0: Y_t\ge\tfrac12\}$. Then $\sigma<\infty$ $P_{x,y,z}$-almost surely, and for every real $s$
--   $$P_{x,y,z}(Z_\sigma\le s)=\begin{cases}0 & \text{if } s<-\tfrac12,\\[2pt] \dfrac{(n-1)(1-2x)}{n-1-2s} & \text{if } x\ge0,\ -y\le s<z,\\[6pt] \dfrac{n-1-2x}{n-1-2s} & \text{if } x<0,\ -y\le s<z,\\[6pt] \dfrac{(n-1)(1+2s)}{n-1-2s} & \text{if } -\tfrac12\le s<-y,\\[4pt] 1 & \text{if } s\ge z.\end{cases}$$
--
--   The distribution of $Z_\sigma$ is what reduces the value at a start with $y<\tfrac12$ to the values on the segment $\{x=y=\tfrac12\}$ (Corollary 3.6).
--
--   **Formalization Note** $\sigma$ is an infimum in $[0,\infty]$; its almost sure finiteness is part of the conclusion, and $Z_\sigma$ is evaluated at $\sigma$.
--
--   Differences from the source:
--   - encoding: Z_σ with σ = inf{t > 0 : Y_t ≥ 1/2} → σ is an infimum in [0, ∞], asserted finite a.s.; Z is evaluated at σ (time-0 value on the null set {σ = ∞}); reason: the paper uses Z_σ, which presupposes σ < ∞ a.s.
--   - encoding: the Markov family (P_{x,y,z}) of p.11 → (X, Y, Z) is constructed from (x, y, z) on the same noise (B, θ): radius ||x| + B_t|, a fixed ray (0 if x ≥ 0, 1 if x < 0) until the first zero, initial ribs y on ray 0 and −z on ray 1; P_{x,y,z} is the law of this construction; reason: a concrete realization of the paper's family of initial distributions
--   - reading: P_{x,y,z}((X_0, Y_0, Z_0) = (x, y, z)) = 1 for every (x, y, z) ∈ D → the start (−y, y, −y), y > 0, is the identified point (y, y, −y) (a ray becomes the longest the moment its rib reaches Y); reason: Remark 3.7: "the points (−y, y, −y) and (y, y, −y) in the state space correspond to the same value of U"; the jump rule of p.11
--   - encoding: B is a Brownian motion (a.s. continuous paths, B_0 = 0 a.s.) → every path of B is continuous and starts at 0, and every B_t is measurable; reason: the paper's Brownian motion (Revuz–Yor) is the continuous version; every Brownian motion has such a version
--   - encoding: rays R_k, k = 1, …, n, and complex signs uniform on {e^{2πik/n}} → rays indexed from 0 (Fin n, resp. ℕ); index k is the paper's ray k + 1; the sign θ_m is recorded by its ray index; reason: relabelling; same instances
--   - encoding: the countable set of excursions "can be ordered by the set of natural numbers" (order unspecified) → excursion number = least k such that the k-th enumerated nonnegative rational lies in the excursion; reason: one concrete injective, path-measurable numbering; the law of the spider does not depend on the numbering
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Lemma 3.2, p.12

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_GeneralProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Lemma 3.2 (law of `Z_σ`)** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Lemma 3.2,
p.12): "Let y < 1/2 and σ = inf{t > 0 : Y_t ≥ 1/2}. Then the distribution of Z_σ under P_{x,y,z}
is determined by P_{x,y,z}(Z_σ ≤ s) = 0 if s < −1/2; (n−1)(1−2x)/(n−1−2s) if x ≥ 0, −y ≤ s < z;
(n−1−2x)/(n−1−2s) if x < 0, −y ≤ s < z; (n−1)(1+2s)/(n−1−2s) if −1/2 ≤ s < −y; 1 if s ≥ z."

For every `(x, y, z) ∈ 𝒟` with `y < 1/2`: `σ < ∞` almost surely, and for every real `s` the
probability that `Z_σ ≤ s` is the displayed piecewise function of `s`.

**Formalization Note.** `σ` is an infimum in `[0, ∞]`; `Z_σ` is evaluated at `σ`, which is finite
almost surely (asserted). The five cases are disjoint on `𝒟` and are tested in the printed order. -/
theorem lemma_3_2 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : SpiderNoise n P) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace)
    (hy : y < 1 / 2) :
    let σ : Ω → ℝ≥0∞ := fun ω =>
      sInf {u : ℝ≥0∞ | ∃ t : ℝ≥0, u = t ∧ 0 < t ∧ 1 / 2 ≤ Yg N x y z t ω}
    (∀ᵐ ω ∂P, σ ω < ⊤) ∧
    ∀ s : ℝ, P {ω | atTime (Zg N x y z) σ ω ≤ s} = ENNReal.ofReal
      (if s < -1 / 2 then 0
       else if 0 ≤ x ∧ -y ≤ s ∧ s < z then ((n : ℝ) - 1) * (1 - 2 * x) / ((n : ℝ) - 1 - 2 * s)
       else if x < 0 ∧ -y ≤ s ∧ s < z then ((n : ℝ) - 1 - 2 * x) / ((n : ℝ) - 1 - 2 * s)
       else if -1 / 2 ≤ s ∧ s < -y then ((n : ℝ) - 1) * (1 + 2 * s) / ((n : ℝ) - 1 - 2 * s)
       else 1) := by sorry

end SpiderDiameter
