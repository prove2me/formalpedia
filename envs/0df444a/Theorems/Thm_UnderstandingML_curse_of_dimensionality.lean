-- Prove2me | Theorems.Thm_UnderstandingML_curse_of_dimensionality
-- name    : UnderstandingML.curse_of_dimensionality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:56:53.030732+00:00
-- url     : https://prove2.me/theorems/a02639ea-4da6-4b13-adf4-d72791ae0125
-- title:
--   Theorem 19.4: for integer c ≥ 2 and any learning rule, some distribution on [0,1]^d × {0,1} with c-Lipschitz η and Bayes error 0 forces expected error ≥ 1/4 when 2m ≤ (c+1)^d
-- statement:
--   **Theorem 19.4.** For any $c > 1$, and every learning rule, $L$, there exists a distribution over $[0,1]^d \times \{0,1\}$, such that $\eta(x)$ is $c$-Lipschitz, the Bayes error of the distribution is $0$, but for sample sizes $m \le (c+1)^d/2$, the true error of the rule $L$ is greater than $1/4$.
--
--   As the proof gives it (the grid $G^d_c$ with spacing $1/c$ and Theorem 5.1): $c \ge 2$ is an integer, the sample size $m$ with $2m \le (c+1)^d$ is fixed before the distribution, and the true error of $L$ is at least $1/4$ in expectation over $S \sim D^m$ (Equation (5.2) of the proof of Theorem 5.1).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.2.2 p. 263, Theorem 19.4 with its proof (via Theorem 5.1)

import Definitions.Def_UnderstandingML_NearestNeighbor

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 19.4** (p. 263). For any `c > 1` and every learning rule `L`, there exists a
distribution over `[0,1]^d × {0,1}` such that `η(x)` is `c`-Lipschitz, the Bayes error of the
distribution is `0`, but for sample sizes `m ≤ (c+1)^d / 2` the true error of the rule `L` is
greater than `1/4`.
As the proof (via Theorem 5.1) gives it: `c ≥ 2` is an integer (the grid has spacing `1/c`),
the sample size `m` is fixed first, and the true error is at least `1/4` in expectation over
`S ∼ D^m`. -/
theorem curse_of_dimensionality (d c : ℕ) (hc : 2 ≤ c)
    (L : Learner (cube d × Bool) (cube d → Bool)) (m : ℕ) (hm : 2 * m ≤ (c + 1) ^ d) :
    ∃ (DX : Measure (cube d)) (η : cube d → ℝ), IsProbabilityMeasure DX ∧
      LipschitzWith c η ∧ (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) ∧
      risk loss01 (condLaw DX η) (bayesRule η) = 0 ∧
      1 / 4 ≤ ∫ S, risk loss01 (condLaw DX η) (L m S) ∂(iidLaw (condLaw DX η) m) := by sorry

end UnderstandingML
