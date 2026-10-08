-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_5_5
-- name    : PoissonDepTrials.SecondOrder.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:29.817205+00:00
-- url     : https://prove2.me/theorems/853bc4d4-23ba-428a-8c4a-2c42ea1ef3a6
-- title:
--   Lemma 5.5, p. 544 — the bound (5.6) on |U_bU_λh(w)| for b ≤ λ
-- statement:
--   Let $0<b\le\lambda$ and $|h(k)|\le M$ for all $k$. Let $U_bU_\lambda h(w)=\Delta S_b(U_\lambda h)(w+1)$. Then for every integer $w\ge0$,
--   $$\begin{aligned}\bigl|U_bU_\lambda h(w)\bigr|\le4(\lambda b)^{-1}M\Bigl[&1+|1+b-\lambda|+\bigl(b^{1/2}+|w+2-\lambda|+3|w+1-\lambda|\bigr)\min(\lambda^{-1/2},1)\\&+(2+4|1+b-\lambda|)\,|w+1-\lambda|\min(b^{-1/2},1)\Bigr].\end{aligned}$$
--
--   Applied with $b=\lambda^{(i)}$ at the random point $W^{(i,j)}=\sum_{k\ne i,j}X_k$, it bounds the remainder of the second application of (5.8) and produces the term $96\lambda^{-1}\sum_i\sum_{j\ne i}p_i^2p_j^2/\lambda^{(i)}$ of (5.9).
--
--   **Formalization Note** $b>0$ is the standing range of §5. $\|h\|$ is replaced by a bound $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 544, Lemma 5.5, (5.6)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.5, (5.6), p. 544: for `0 < b ≤ λ` and every `w ≥ 0`,
`|U_bU_λh(w)| ≤ 4(λb)^{−1}‖h‖[1 + |1 + b − λ| + (b^{1/2} + |w + 2 − λ| + 3|w + 1 − λ|) min(λ^{−1/2}, 1)
  + (2 + 4|1 + b − λ|)|w + 1 − λ| min(b^{−1/2}, 1)]`. -/
theorem lemma_5_5 (lam b : ℝ) (hb : 0 < b) (hbl : b ≤ lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, |stU b (stU lam h) w| ≤
      4 * (lam * b)⁻¹ * M * (1 + |1 + b - lam| +
        (Real.sqrt b + |(w : ℝ) + 2 - lam| + 3 * |(w : ℝ) + 1 - lam|) * min (1 / Real.sqrt lam) 1 +
        (2 + 4 * |1 + b - lam|) * |(w : ℝ) + 1 - lam| * min (1 / Real.sqrt b) 1) := by sorry

end PoissonDepTrials.SecondOrder
