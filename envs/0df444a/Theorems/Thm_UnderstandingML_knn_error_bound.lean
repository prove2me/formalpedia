-- Prove2me | Theorems.Thm_UnderstandingML_knn_error_bound
-- name    : UnderstandingML.knn_error_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:57:50.541833+00:00
-- url     : https://prove2.me/theorems/880657ca-8e9b-4c03-9cc6-e5c27a47301f
-- title:
--   Theorem 19.5: for c-Lipschitz η on [0,1]^d and k ≥ 10, the k-NN rule has E_S[L_D(h_S)] ≤ (1 + √(8/k)) L_D(h⋆) + (6c√d + k) m^{−1/(d+1)}
-- statement:
--   **Theorem 19.5.** Let $X = [0,1]^d$, $Y = \{0,1\}$, and $D$ be a distribution over $X \times Y$ for which the conditional probability function, $\eta$, is a $c$-Lipschitz function. Let $h_S$ denote the result of applying the $k$-NN rule to a sample $S \sim D^m$, where $k \ge 10$. Let $h^\star$ be the Bayes optimal hypothesis. Then
--   $$\mathbb{E}_S[L_D(h_S)] \le \Big(1 + \sqrt{\tfrac{8}{k}}\Big) L_D(h^\star) + \big(6c\sqrt{d} + k\big)\, m^{-\frac{1}{d+1}}.$$
--
--   Formally: $D = $ `condLaw DX η` with $\eta$ valued in $[0,1]$, $h$ any majority $k$-NN rule (any tie-breaking), measurable in $(S, x)$, and $m \ge k$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.6 p. 265, Theorem 19.5 (Exercises 1-4)

import Definitions.Def_UnderstandingML_NearestNeighbor

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 19.5** (p. 265). Let `X = [0,1]^d`, `Y = {0,1}`, and `D` be a distribution over
`X × Y` for which the conditional probability function `η` is a `c`-Lipschitz function. Let
`h_S` denote the result of applying the `k`-NN rule to a sample `S ∼ D^m`, where `k ≥ 10`.
Let `h⋆` be the Bayes optimal hypothesis. Then
`E_S[L_D(h_S)] ≤ (1 + √(8/k)) L_D(h⋆) + (6 c √d + k) m^{−1/(d+1)}`.
Here `D = condLaw D_X η`, the rule is any `k`-NN (majority) rule, measurable in `(S, x)`,
and `m ≥ k`. -/
theorem knn_error_bound (d : ℕ) (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 10 ≤ k) (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsKNNRule k h)
    (hmeas : ∀ m, Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ h m p.1 p.2))
    (m : ℕ) (hm : k ≤ m) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤
      (1 + Real.sqrt (8 / k)) * risk loss01 (condLaw DX η) (bayesRule η) +
        (6 * c * Real.sqrt d + k) * (m : ℝ) ^ (-(1 : ℝ) / (d + 1)) := by sorry

end UnderstandingML
