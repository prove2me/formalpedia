-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_simplex_means
-- name    : RSCapacity.ListDecoding.simplex_means
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:01.981167+00:00
-- url     : https://prove2.me/theorems/c66f40b9-e5f3-4719-94aa-f443f32aca57
-- title:
--   Fact 4.3 — coordinate means, total mean and harmonic asymptotic
-- statement:
--   For $d\ge1$, $W>0$, let $D$ be uniform on the entire finite set $\Lambda_d(W)=\{b\in\mathbb N^d:\sum_{i=1}^d ib_i\le W\}$. Write $H_d=\sum_{i=1}^d1/i$. There is an absolute $c>0$ such that, for every $d\ge1$, there is a constant $B_d>0$, independent of $W$ and the coordinate, for which $W\ge cd^4$ implies both
--   $$\left|\mathbb E_D[b_i]-\frac{W}{i(d+1)}\right|\le B_d\quad(1\le i\le d),\qquad
--   \left|\mathbb E_D\!\left[\sum_{i=1}^d b_i\right]-\frac{WH_d}{d+1}\right|\le B_d.$$
--   The full consequent also retains
--   $$\lim_{d\to\infty}(H_d-\log d)=\gamma,$$
--   where $\gamma$ is the Euler–Mascheroni constant. Expectations are normalized finite sums. The estimate supplies the source's additive, dimension-dependent control of allowed exponent totals.
--
--   Differences from the source:
--   - encoding: W = Ω(d⁴), coordinate indices 1,…,d, and additive O_d(1) terms → an absolute threshold c, positive B_d before W and i, coordinate i.val+1, and both explicit absolute-error bounds; reason: finite maxima combine the coordinate and total constants without changing the estimates; the harmonic o(1) is its equivalent limit statement
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Fact 4.3, p.15; Appendix B, pp.26–27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Counting

open scoped Topology

namespace RSCapacity.ListDecoding

/-- Fact 4.3, submission #495 p.15, including the consequent and the
harmonic asymptotic. The additive error depends on d, never on W or i. -/
theorem simplex_means :
    (∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 0 < d →
      ∃ B : ℝ, 0 < B ∧ ∀ W : ℝ, 0 < W → c * (d : ℝ) ^ 4 ≤ W →
        (∀ i : Fin d,
          |coordinateMean d W i - W / ((i.val + 1 : ℕ) * (d + 1 : ℕ))| ≤ B) ∧
        |totalMean d W - W * harmonic d / (d + 1 : ℕ)| ≤ B) ∧
    Filter.Tendsto (fun d : ℕ => harmonic d - Real.log d)
      Filter.atTop (𝓝 Real.eulerMascheroniConstant) := by sorry

end RSCapacity.ListDecoding
