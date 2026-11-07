-- Prove2me | Theorems.Thm_PlantedIQP_lemma_30
-- name    : PlantedIQP.lemma_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:22.754366+00:00
-- url     : https://prove2.me/theorems/74fdc771-372c-483f-b1e6-b91e9d7fe16f
-- title:
--   Lemma 30 — $m_1=1$, $m_2=3-2^{1-n}$, $m_3=15-30\cdot2^{-n}+16\cdot4^{-n}$
-- statement:
--   For the law $M(n)$ with any cubic-part distribution $D$, the normalized moments $m_k=2^{nk}\mathbb E_{f\leftarrow M(n)}p_f(0)^k$ satisfy, with $t=2^{-n}$, for every $n$:
--
--   $$
--   m_1=1,\qquad m_2=3-2t,\qquad m_3=15-30t+16t^2 .
--   $$
--
--   Consequently, for every family of distributions $D(n)$ and $k=1,2,3$,
--
--   $$
--   m_k\longrightarrow(2k-1)!!\qquad(n\to\infty),
--   $$
--
--   which is the source's $m_k=(2k-1)!!+o(1)$ (so $m_2=3+o(1)$ and $m_3=15+o(1)$, Eq. (34)).
--
--   The second and third moments give the mean $m_2-1$ and the variance $m_3-m_2^2$ of the single-shot XEB score.
--
--   Differences from the source:
--   - generalization: m_k = (2k − 1)!! + o(1) for k = 1, 2, 3 → the exact values m₁ = 1, m₂ = 3 − 2t, m₃ = 15 − 30t + 16t² (t = 2^{−n}) for every n and D, together with the limit form for every family D(n); reason: the exact values imply the o(1) form, which is also stated; the completeness bound for all n ≥ 1 needs them
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Lemma 30, Eq. (24), p.20 (and Eq. (34), p.21)

import Mathlib
import Definitions.Def_PlantedIQP_moment

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Lemma 30, p.20, with Eq. (34), p.21: for `k = 1, 2, 3` the normalized
moments of `M(n)` are `m_k = 2^{nk} E_{f←M(n)} p_f(0)^k = (2k − 1)!! + o(1)`. Stated with the exact values,
for every `n` and every cubic-part law `D` (`t = 2^{−n}`): `m₁ = 1`, `m₂ = 3 − 2t`,
`m₃ = 15 − 30t + 16t²`; and the source's limit form, for every family of laws `D(n)`. -/
theorem lemma_30 :
    (∀ (n : ℕ) (D : PMF (CubicPoly n)),
      moment n 1 D = 1 ∧ moment n 2 D = 3 - 2 * ((2 : ℝ) ^ n)⁻¹ ∧
        moment n 3 D = 15 - 30 * ((2 : ℝ) ^ n)⁻¹ + 16 * (((2 : ℝ) ^ n)⁻¹) ^ 2) ∧
      ∀ (D : (n : ℕ) → PMF (CubicPoly n)) (k : ℕ), 1 ≤ k → k ≤ 3 →
        Filter.Tendsto (fun n => moment n k (D n)) Filter.atTop
          (nhds ((Nat.doubleFactorial (2 * k - 1) : ℕ) : ℝ)) := by sorry

end PlantedIQP
