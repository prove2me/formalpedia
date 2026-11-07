-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_3_1
-- name    : SubmodSparsify.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:39.024705+00:00
-- url     : https://prove2.me/theorems/aa66b4a3-dcde-4dd3-8b7e-911b1775aac6
-- title:
--   Lemma 3.1 — concentration for $\min\{1, p_i\Lambda\}$-sampling: $\Pr[|\sum_i Y_i| > \eta\sum_i z_i + xR/(\eta\Lambda)] \le 2e^{-x}$
-- statement:
--   Let $p_1, \dots, p_m > 0$ and $\Lambda > 1$. Sample each component $i$ independently with probability $\min\{1, p_i \Lambda\}$ and set $W_i := 1/\min\{1, p_i\Lambda\}$ if it is sampled and $W_i := 0$ otherwise. For $z_1, \dots, z_m \ge 0$ let $Y_i := (W_i - 1) z_i$ and $R := \max_{i \in [m]} z_i / p_i$. Then for every $0 < \eta \le 1$ and $x > 0$,
--
--   $$\Pr\Bigl[\Bigl|\sum_{i=1}^m Y_i\Bigr| > \eta \sum_{i=1}^m z_i + \frac{x R}{\eta \Lambda}\Bigr] \le 2 e^{-x}.$$
--
--   The bound is in mixed multiplicative–additive form because the sum $\sum_i z_i$ is not normalized; it is applied to every increment vector of the chaining argument.
--
--   Differences from the source:
--   - encoding: f_i sampled independently with probability min{1, p_iΛ}; components indexed by [m] → ξ : Fin m → Bool under the product law bernProb with q_i = min 1 (Λ * p_i); W_i = sampledWeight p Λ ξ i; reason: the finite product Bernoulli law; same distribution
--   - encoding: R := max_{i∈[m]} z_i/p_i → ⨆ i, z i / p i (the maximum over the finite index set; 0 when m = 0, where both sides of the event are 0); reason: same value for m ≥ 1
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 3.1, p.16 (PDF p.18); proof, Appendix C.1, p.60 (PDF p.62)

import Mathlib
import Definitions.Def_SubmodSparsify_bernProb

namespace SubmodSparsify

/-- **Lemma 3.1** (p.16): concentration for `min{1, Λp}`-sampling.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 3.1, p.16.

Let `p₁, …, p_m > 0` and `Λ > 1`, and sample each component independently with probability
`min{1, pᵢΛ}`, with weight `Wᵢ = 1/min{1, pᵢΛ}` if sampled and `0` otherwise. For any
`z₁, …, z_m ≥ 0` put `Yᵢ := (Wᵢ − 1)zᵢ` and `R := max_{i∈[m]} zᵢ/pᵢ`. Then for any `0 < η ≤ 1`
and `x > 0`,
`Pr[|Σᵢ Yᵢ| > η Σᵢ zᵢ + xR/(ηΛ)] ≤ 2e^{−x}`.

**Formalization Note.** The sample is `ξ : Fin m → Bool` with the product Bernoulli law
`bernProb (sampleProb p Λ)` (`sampleProb p Λ i = min 1 (Λ * pᵢ)`), and `Wᵢ` is
`sampledWeight p Λ ξ i` (module `SubmodSparsify.bernProb`). `R` is the supremum `⨆ i, zᵢ/pᵢ`
over the finite index set (the maximum; `0` when `m = 0`, where both sides of the event are `0`). -/
theorem lemma_3_1 {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (Λ : ℝ) (hΛ : 1 < Λ)
    (z : Fin m → ℝ) (hz : ∀ i, 0 ≤ z i) (η x : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hx : 0 < x) :
    bernProb (sampleProb p Λ) (fun ξ =>
        η * ∑ i, z i + x * (⨆ i, z i / p i) / (η * Λ) <
          |∑ i, (sampledWeight p Λ ξ i - 1) * z i|) ≤
      2 * Real.exp (-x) := by sorry

end SubmodSparsify
