-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_5_1
-- name    : PoissonDepTrials.SecondOrder.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:51:54.922832+00:00
-- url     : https://prove2.me/theorems/278bce03-299b-4d75-8636-d830342dc9a9
-- title:
--   Lemma 5.1, p. 543 — |e^{−λ}λ^k − e^{−b}b^k| ≤ (λ − b)(e^{−λ}kλ^{k−1} + e^{−b}b^k) for λ ≥ b > 0
-- statement:
--   For real numbers $\lambda\ge b>0$ and every integer $k\ge0$,
--   $$\bigl|e^{-\lambda}\lambda^k-e^{-b}b^k\bigr|\le(\lambda-b)\bigl(e^{-\lambda}k\lambda^{k-1}+e^{-b}b^k\bigr).$$
--
--   This is a Lipschitz-type estimate of the Poisson weights in the parameter; summed against $h(k)/k!$ it gives Lemma 5.2.
--
--   **Formalization Note** At $k=0$ the term $k\lambda^{k-1}$ is $0$, as on the page.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 543, Lemma 5.1, (5.1)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.1, (5.1), p. 543: for `λ ≥ b > 0` and `k = 0, 1, 2, …`,
`|e^{−λ}λ^k − e^{−b}b^k| ≤ (λ − b)(e^{−λ}kλ^{k−1} + e^{−b}b^k)`. -/
theorem lemma_5_1 (lam b : ℝ) (hb : 0 < b) (hbl : b ≤ lam) (k : ℕ) :
    |Real.exp (-lam) * lam ^ k - Real.exp (-b) * b ^ k| ≤
      (lam - b) * (Real.exp (-lam) * k * lam ^ (k - 1) + Real.exp (-b) * b ^ k) := by sorry

end PoissonDepTrials.SecondOrder
