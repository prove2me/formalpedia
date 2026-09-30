-- Prove2me | Theorems.Thm_UnderstandingML_knn_label_lemma
-- name    : UnderstandingML.knn_label_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:57:30.945885+00:00
-- url     : https://prove2.me/theorems/0419b625-bb73-4e0e-8a5f-a8375b72520c
-- title:
--   Lemma 19.7: for k ≥ 10 independent Bernoulli(pᵢ) labels with mean p, E P_{y∼p}[y ≠ 𝟙[p' > 1/2]] ≤ (1 + √(8/k)) P_{y∼p}[y ≠ 𝟙[p > 1/2]]
-- statement:
--   **Lemma 19.7.** Let $k \ge 10$ and let $Z_1, \dots, Z_k$ be independent Bernoulli random variables with $P[Z_i = 1] = p_i$. Denote $p = \frac1k\sum_i p_i$ and $p' = \frac1k\sum_{i=1}^k Z_i$. Then
--   $$\mathbb{E}_{Z_1, \dots, Z_k}\, P_{y \sim p}\big[y \ne \mathbb{1}[p' > 1/2]\big] \le \Big(1 + \sqrt{\tfrac{8}{k}}\Big)\, P_{y \sim p}\big[y \ne \mathbb{1}[p > 1/2]\big].$$
--
--   Formally: $p_i \in [0,1]$, the $Z_i$ have the product law of the Bernoulli laws, $\mathbb{1}[p' > 1/2]$ is the majority of the $Z_i$, and $P_{y \sim p}[y \ne y'] = $ `bernoulliErr p y'`.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.6 p. 266, Lemma 19.7 (Exercise 2)

import Definitions.Def_UnderstandingML_NearestNeighbor

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 19.7** (p. 266). Let `k ≥ 10` and let `Z₁, …, Z_k` be independent Bernoulli random
variables with `P[Zᵢ = 1] = pᵢ`. Denote `p = (1/k) ∑ᵢ pᵢ` and `p' = (1/k) ∑ᵢ Zᵢ`. Then
`E_{Z₁, …, Z_k} P_{y ∼ p}[y ≠ 𝟙[p' > 1/2]] ≤ (1 + √(8/k)) P_{y ∼ p}[y ≠ 𝟙[p > 1/2]]`.
Here `𝟙[p' > 1/2]` is the majority of the `Zᵢ` and `P_{y ∼ p}[y ≠ y'] = bernoulliErr p y'`. -/
theorem knn_label_lemma (k : ℕ) (hk : 10 ≤ k) (p : Fin k → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∫ Z, bernoulliErr ((∑ i, p i) / k) (majority Z) ∂(Measure.pi (fun i ↦ bernoulliLaw (p i))) ≤
      (1 + Real.sqrt (8 / k)) * bernoulliErr ((∑ i, p i) / k) (decide (1 / 2 < (∑ i, p i) / k)) := by sorry

end UnderstandingML
