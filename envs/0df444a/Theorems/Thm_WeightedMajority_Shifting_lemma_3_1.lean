-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_lemma_3_1
-- name    : WeightedMajority.Shifting.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:36.159+00:00
-- url     : https://prove2.me/theorems/3bf1c216-9402-4007-b8ea-5f24e9b85831
-- title:
--   Lemma 3.1 — WML makes at most (log(n/(βγ)) + m₀ log(1/β))/log(1/u) mistakes, and keeps the weight floor
-- statement:
--   Let $0 < \beta < 1$ and $0 < \gamma < \tfrac12$, and put $u = \frac{1+\beta}{2} + (1-\beta)\gamma$. Consider a pool of $n \ge 1$ algorithms and any finite sequence $\mathcal S$ of trials with binary predictions and labels, and let $m_0$ be the minimum, over the members of the pool, of the number of mistakes made on $\mathcal S$. Run WML with parameters $\beta, \gamma$ on $\mathcal S$, from positive initial weights $w_i^{\mathrm{init}}$ such that every initial weight is at least $\beta\gamma/n$ times the total initial weight:
--   $$w_i^{\mathrm{init}} \ge \frac{\beta\gamma}{n}\sum_{j} w_j^{\mathrm{init}} \quad \text{for every } i .$$
--   Then:
--
--   1. the number $m$ of mistakes made by WML on $\mathcal S$ satisfies
--   $$m \le \frac{\log\big(n/(\beta\gamma)\big) + m_0 \log(1/\beta)}{\log(1/u)} ;$$
--   2. the final weights satisfy the same floor: $w_i^{\mathrm{fin}} \ge \frac{\beta\gamma}{n}\sum_j w_j^{\mathrm{fin}}$ for every $i$.
--
--   The bound depends on the length of the sequence only through $m_0$, and the second part allows the lemma to be applied again, from the final weights, to a following block of trials; this is how Theorem 3.1 is obtained.
--
--   **Formalization Note** The base of the logarithm cancels in the ratio, so the natural logarithm `Real.log` is used. The paper allows $\gamma = 0$ for the algorithm, but then the bound is $\log(n/0) = +\infty$ and says nothing; in Lean $n/0 = 0$ would make the literal statement false, so $\gamma > 0$ is assumed. The pool is `Fin n` with $n > 0$; the sequence has $T$ trials and $m_0$ is `bestMistakesOn x ρ 0 T`. The initial weights are arbitrary positive reals subject to the floor, so the lemma applies to any starting point of a run.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), pp. 223–224, Lemma 3.1

import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML

namespace WeightedMajority.Shifting

theorem lemma_3_1 {n T : ℕ} (hn : 0 < n) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i) :
    (masterMistakes ρ lam : ℝ) ≤
        (Real.log ((n : ℝ) / (β * γ)) + (bestMistakesOn x ρ 0 T : ℝ) * Real.log (1 / β)) /
          Real.log (1 / uFactor β γ) ∧
      ∀ i, β * γ / (n : ℝ) * totalWeight (w T) ≤ w T i := by sorry

end WeightedMajority.Shifting
