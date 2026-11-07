-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_13
-- name    : PrivRobustStat.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:09.465218+00:00
-- url     : https://prove2.me/theorems/e4534046-6e6d-4ea8-831f-6c2eddd01c50
-- title:
--   Lemma 13, p.30 — Algorithm 6 is $(\varepsilon,\delta)$-DP and returns $q$ with $\|q-\mu\|_2\le12\sqrt d$ w.p. $1-\beta$
-- statement:
--   **Lemma 13** (private localization). Algorithm 6 with public $\varepsilon\in(0,1]$, $\delta\in(0,\tfrac14)$ is $(\varepsilon,\delta)$-differentially private on $(\mathbb R^d)^n$, for every $d$ and $n$.
--
--   Moreover, there is an absolute constant $C>0$ such that the following holds. Let $D$ satisfy Model 1 with mean $\mu$, let $\alpha\in(0,\tfrac1{32})$, $\beta\in(0,\tfrac14)$, and
--
--   $$n\ge C\Big(\frac d\varepsilon\log\frac{nd}{\beta\delta}+\log\frac d\beta\Big).\tag{37}$$
--
--   Draw $x^\circ_{[n]}$ i.i.d. from $D$ and let any adversary replace at most $\alpha n$ points. Then with probability at least $1-\beta$ over the sample and the Laplace noise, Algorithm 6 returns $q$ with
--
--   $$\|q-\mu\|_2\le12\sqrt d .$$
--
--   Localization supplies the public centre and radius that the private filter needs.
--
--   **Formalization Note** "With probability at least $1-\beta$" is the lower integral over the clean sample of the inner probability over the noise, for every adversary, measurable or not.
--
--   Differences from the source:
--   - encoding: Laplace draws η_{a,k}, one per occupied bin → draws indexed by (a, first sample index in bin k), i.i.d. Lap(2/ε_h); reason: distinct occupied bins get distinct independent coordinates: same joint law
--   - reading: "Algorithm 6 is (ε, δ)-private" → for every d, n and every pair of neighbouring datasets in (ℝ^d)^n, ε ∈ (0, 1], δ ∈ (0, 1/4); reason: DP is a worst-case notion (p.12); these are Algorithm 6's input ranges
--   - encoding: the output law of the mechanism → the law is the pushforward of the noise measure, and the item also asserts the output map is measurable; reason: Lean pushes a non-measurable map to the zero measure, under which privacy would hold vacuously; measurability rules this out and changes no instance
--   - reading: with probability at least 1 − β on an α-corrupted sample under Model 1 → lower integral over D^⊗n of the inner probability over the noise, for every adversary replacing at most αn points; reason: meaningful for non-measurable adversaries; for a measurable adversary it is at least the probability of the joint event
--   - encoding: Model 1 → probability measure with MemLp id 2 and E⟨u, x − µ⟩² ≤ ∥u∥² for all u, µ the Bochner mean; reason: the mean and covariance exist exactly under a finite second moment
--   - encoding: "for an absolute constant C > 0" → ∃ C > 0 before d, n, D and the parameters; reason: meaning of an absolute constant
--   - encoding: "It runs in time O(nd log n)" → not in this item; the mission goal theorem_4 bounds the work of a machine program; reason: the item states the algorithm as a random map of data and noise, which has no cost (planning decision 10)
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 13, pp.30–31 (PDF pp.33–34); Algorithm 6, p.31

import Mathlib
import Definitions.Def_PrivRobustStat_MeanEst

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 13** (private localization), pp.30–31 (PDF pp.33–34).

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Algorithm 6 is (ε, δ)-private. For α ∈ (0, 1/32) and β ∈ (0, 1/4), on an α-corrupted sample under
Model 1, it returns q satisfying ∥q − µ∥₂ ≤ 12√d with probability at least 1 − β, provided
n ≥ C( d/ε log(nd/(βδ)) + log(d/β) ) (37) for an absolute constant C > 0. It runs in time
O(nd log n)."

**Formalization Note.**
* Algorithm 6's public inputs are `ε ∈ (0, 1]`, `δ ∈ (0, 1/4)` (p.31). Privacy holds for every `d`,
  `n` and every pair of neighbouring datasets in `(ℝ^d)^n`; the first part also asserts that the
  output is a measurable function of the Laplace draws (`lapNoise`, i.i.d. `Lap(2d/ε)`).
* An α-corrupted sample under Model 1 (Definition 1): `n` i.i.d. points from a Model-1 distribution
  `D`, then any adversary `A` (measurable or not) that replaces at most `αn` points. "With
  probability at least 1 − β" over both the sample and the noise is the lower integral over the
  clean sample of the inner probability over the noise; this is at least as strong as the
  probability of the joint event for every measurable adversary, and meaningful for every adversary.
* The constant `C` is chosen before `d`, `n`, `D` and the parameters. The running time is carried by
  the goal theorem's time clause. -/
theorem lemma_13 :
    (∀ (d n : ℕ) (ε δ : ℝ), 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 4 →
      (∀ x : Fin n → Vec d, Measurable fun η : Fin d × Fin n → ℝ => alg6 x ε δ η) ∧
      IsApproxDP (fun x : Fin n → Vec d =>
        (lapNoise d n (alg6Scale d ε)).map fun η => alg6 x ε δ η) ε δ) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ) (D : Measure (Vec d)) [IsProbabilityMeasure D], IsModel1 D →
        ∀ α β ε δ : ℝ, 0 < α → α < 1 / 32 → 0 < β → β < 1 / 4 → 0 < ε → ε ≤ 1 → 0 < δ →
          δ < 1 / 4 →
          C * ((d : ℝ) / ε * Real.log ((n : ℝ) * d / (β * δ)) + Real.log ((d : ℝ) / β)) ≤ n →
          ∀ A : (Fin n → Vec d) → (Fin n → Vec d), IsAdversary α A →
            ENNReal.ofReal (1 - β) ≤
              ∫⁻ X, innerProb (lapNoise d n (alg6Scale d ε))
                {η | ‖alg6 (A X) ε δ η - popMean D‖ ≤ 12 * Real.sqrt d}
                ∂(Measure.pi fun _ : Fin n => D) := by sorry

end PrivRobustStat
