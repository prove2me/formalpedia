-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_15
-- name    : PrivRobustStat.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:15.671665+00:00
-- url     : https://prove2.me/theorems/b503a4f5-b7ec-452a-a70b-3af67aef11c6
-- title:
--   Lemma 15, p.33 (corrected: $\beta\in(0,\tfrac14)$) — with probability $1-\beta/4$ every $\alpha$-corrupted bounded-covariance sample has a stable good subset $G_0$
-- statement:
--   **Lemma 15.** There are universal constants $C,c>0$ such that the following holds. Let $D$ satisfy Model 1 with mean $\mu$, $\alpha\in(0,c)$, $\beta\in(0,\tfrac14)$ and
--
--   $$n\ge C\,\frac{d\log d+\log(1/\beta)}{\alpha}.$$
--
--   Then with probability at least $1-\beta/4$ over $x^\circ_{[n]}\sim D^{\otimes n}$, for every set $B$ of at most $\alpha n$ indices and every $x_{[n]}$ that agrees with $x^\circ_{[n]}$ off $B$, there is $G_0\subseteq G:=[n]\setminus B$ with
--
--   $$|G_0|\ge(1-C\alpha)n,\qquad \max_{i\in G_0}\|x_i-\mu\|_2\le C\sqrt{d/\alpha},$$
--   $$\Big\|\frac1{|G_0|}\sum_{i\in G_0}x_i-\mu\Big\|_2^2\le C\alpha,\qquad \frac1n\sum_{i\in G_0}(x_i-\mu)(x_i-\mu)^\top\preceq CI.\tag{40}$$
--
--   These deterministic conditions are what the filtering analysis of Theorem 4 uses about the good samples.
--
--   **Formalization Note** The good event is a measurable set of clean samples; the adversary is arbitrary. $\preceq CI$ is written as $\frac1n\sum_{G_0}\langle u,x_i-\mu\rangle^2\le C\|u\|_2^2$ for all $u$.
--
--   Differences from the source:
--   - reading: "with probability ≥ 1 − β/4, every α-corrupted sample x[n] from D with uncorrupted sample indices G admits G0 ⊆ G" → a measurable set S of clean samples with D^⊗n(S) ≥ 1 − β/4 such that for every x° ∈ S, every B with |B| ≤ αn and every x agreeing with x° off B, some G0 ⊆ [n] ∖ B satisfies (40); reason: the strongest reading: one good event for all corruptions, with no outer measure
--   - correction: β (no range stated) → β ∈ (0, 1/4); reason: the paper's range of the failure probability (Problem 1, Lemma 13), and the bound fails near β = 1: at d = 1 the term d log d is 0, so n = 1 is allowed for β close to 1, and one N(0, 1) point lies within √(Cα) of its mean with probability far below 1 − β/4
--   - encoding: (1/n)∑ (x_i − µ)(x_i − µ)⊤ ⪯ CI → (1/n)∑_{G0} ⟨u, x_i − µ⟩² ≤ C∥u∥² for all u; reason: the Loewner order against CI is the quadratic-form bound
--   - encoding: Model 1 → probability measure with MemLp id 2 and E⟨u, x − µ⟩² ≤ ∥u∥² for all u; reason: the mean and covariance exist exactly under a finite second moment
--   - encoding: universal constants C, c > 0 → ∃ C, c > 0 before d, D, n, α, β; reason: meaning of universal constants
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 15, p.33 (PDF p.36); proof in Appendix B.1, p.76

import Mathlib
import Definitions.Def_PrivRobustStat_Model

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 15** (sample stability under bounded covariance), p.33 (PDF p.36); proof in Appendix B.1,
p.76.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Let D be as in Model 1. There are universal constants C, c > 0 such that if
n ≥ C((d log d + log(1/β))/α), and α ∈ (0, c), then with probability ≥ 1 − β/4, every α-corrupted
sample x[n] from D with uncorrupted sample indices G admits a set G₀ ⊆ G satisfying:
|G₀| ≥ (1 − Cα)n, max_{i∈G₀} ∥x_i − µ∥₂ ≤ C√(d/α), ∥(1/|G₀|)∑_{i∈G₀} x_i − µ∥₂² ≤ Cα,
(1/n)∑_{i∈G₀} (x_i − µ)(x_i − µ)⊤ ⪯ CI. (40)"

**Formalization Note.**
* `C, c` are chosen before `d`, `D`, `n`, `α`, `β`; `β ∈ (0, 1/4)`, the paper's range of the failure
  probability (Problem 1, Lemma 13). Near `β = 1` the printed bound is false at `d = 1`: `log d = 0`, so
  `n = 1` is allowed, and a single `N(0, 1)` point lies within `√(Cα)` of the mean with probability far
  below `1 − β/4`.
* "With probability ≥ 1 − β/4, every α-corrupted sample admits": there is a measurable set `S` of
  clean samples `x°[n]` of probability `≥ 1 − β/4` such that for every `x° ∈ S`, every set `B` of at
  most `αn` replaced indices and every `x[n]` agreeing with `x°` off `B`, some `G₀ ⊆ G := [n] \ B`
  satisfies (40) for `x[n]`. The adversary is arbitrary.
* `⪯ CI` is written as the quadratic form bound `(1/n)∑_{G₀} ⟨u, x_i − µ⟩² ≤ C∥u∥²` for all `u`. -/
theorem lemma_15 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (d : ℕ) (D : Measure (Vec d)) [IsProbabilityMeasure D], IsModel1 D →
        ∀ (n : ℕ) (α β : ℝ), 0 < α → α < c → 0 < β → β < 1 / 4 →
          C * (((d : ℝ) * Real.log d + Real.log (1 / β)) / α) ≤ n →
          ∃ S : Set (Fin n → Vec d), MeasurableSet S ∧
            ENNReal.ofReal (1 - β / 4) ≤ (Measure.pi fun _ : Fin n => D) S ∧
            ∀ X0 ∈ S, ∀ B : Finset (Fin n), (B.card : ℝ) ≤ α * n →
              ∀ X : Fin n → Vec d, (∀ i, i ∉ B → X i = X0 i) →
                ∃ G0 : Finset (Fin n), G0 ⊆ Bᶜ ∧ (1 - C * α) * n ≤ (G0.card : ℝ) ∧
                  (∀ i ∈ G0, ‖X i - popMean D‖ ≤ C * Real.sqrt ((d : ℝ) / α)) ∧
                  ‖((G0.card : ℝ)⁻¹ • ∑ i ∈ G0, X i) - popMean D‖ ^ 2 ≤ C * α ∧
                  ∀ u : Vec d,
                    (1 / (n : ℝ)) * ∑ i ∈ G0, (inner ℝ u (X i - popMean D)) ^ 2 ≤ C * ‖u‖ ^ 2 := by sorry

end PrivRobustStat
