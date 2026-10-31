-- Prove2me | Theorems.Thm_ParallelLotteries_f_lt_two_sub
-- name    : ParallelLotteries.f_lt_two_sub
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:56.337744+00:00
-- url     : https://prove2.me/theorems/9c937dcc-7e37-406a-82a2-138cc2bb7547
-- title:
--   The two-item constant $f(p_i,p_j)$ stays below $2-1/k$ and tends to it as $(p_i,p_j)\to(0,1)$
-- statement:
--   Let $k\ge2$ and let $f$ be the function (59). Then
--
--   1. $f(p_i,p_j)<2-\dfrac1k$ whenever $0<p_i<1/k<p_j\le1$;
--   2. $f(p_i,p_j)\to2-\dfrac1k$ as $(p_i,p_j)\to(0,1)$ within $(0,1/k)\times(1/k,1]$.
--
--   So $2-1/k$ is the supremum of the two-item constant $\gamma=f(p_i,p_j)$ and is not attained: in the two-item case of Theorem 2 the welfare ratio is strictly below $2-1/k$.
--
--   Differences from the source:
--   - generalization: "$f(p_i,p_j)=\gamma$ is maximized by taking $p_i\to0$ and $p_j\to1$, in which case it converges to $2-1/k$" → the strict bound $f<2-1/k$ on $0<p_i<1/k<p_j\le1$ together with the convergence; reason: the sentence gives the bound by the limit; the strict form is what the strict conclusion of Theorem 2 needs, and it implies the sentence
--   - reading: the sentence for general $k$ → $k\ge2$; reason: for $k=1$ the region $1/k<p_j\le1$ is empty
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, sentence after (60), p.34

import Mathlib
import Definitions.Def_ParallelLotteries_hf

open Filter Topology

namespace ParallelLotteries

/-- **The two-item bound γ = f(p_i, p_j) stays below 2 − 1/k** — Arnosti–Randolph, SSRN 3370605
(preprint), App. D.2, sentence after (60), p.34: "By Lemma 7, f(p_i, p_j) = γ is maximized by
taking p_i → 0 and p_j → 1, in which case it converges to 2 − 1/k."

For every `k ≥ 2`:
1. `f(p_i, p_j) < 2 − 1/k` whenever `0 < p_i < 1/k < p_j ≤ 1`;
2. `f(p_i, p_j) → 2 − 1/k` as `(p_i, p_j) → (0, 1)` within `(0, 1/k) × (1/k, 1]`.

**Formalization Note.** Clause 1 says more than the printed sentence, which gives only the bound
by the limit: it is the strict form the proof of Theorem 2 needs for `k ≥ 2`. For `k = 1` the
region is empty. -/
theorem f_lt_two_sub (k : ℕ) (hk : 2 ≤ k) :
    (∀ pi pj : ℝ, 0 < pi → pi < 1 / (k : ℝ) → 1 / (k : ℝ) < pj → pj ≤ 1 →
      fval k pi pj < 2 - 1 / (k : ℝ)) ∧
    Tendsto (fun q : ℝ × ℝ => fval k q.1 q.2)
      (𝓝[Set.Ioo 0 (1 / (k : ℝ)) ×ˢ Set.Ioc (1 / (k : ℝ)) 1] ((0 : ℝ), (1 : ℝ)))
      (𝓝 (2 - 1 / (k : ℝ))) := by sorry

end ParallelLotteries
