-- Prove2me | Theorems.Thm_StaticProphetSec_hoeffding_monotonicity
-- name    : StaticProphetSec.hoeffding_monotonicity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:32.738761+00:00
-- url     : https://prove2.me/theorems/60d51eb9-c451-40a2-b535-c655825518e7
-- title:
--   Proof of Lemma 3 — $\mathbb P(\mathrm{Bin}(n,k/n)\le j)$ for $j<k$ is monotone in $n$ (corrected: increasing in $n$)
-- statement:
--   For $1\le k\le n$ and $j<k$,
--
--   $$\mathbb P\big(\mathrm{Bin}(n,k/n)\le j\big)\le\mathbb P\big(\mathrm{Bin}(n+1,k/(n+1))\le j\big).$$
--
--   The proof of Lemma 3 draws this from Theorem 4 of Hoeffding (1956). It gives the inequality $\mathbb E[\mathrm{UT}_k(\mathrm{Bin}(n,k/n))]\ge\lim_{m\to\infty}\mathbb E[\mathrm{UT}_k(\mathrm{Bin}(m,k/m))]$.
--
--   Differences from the source:
--
--   - correction: $\mathbb P(\mathrm{Bin}(n,k/n)\le j)$ is decreasing in $n$ → increasing in $n$; reason: the printed claim is false: for $k=1$, $j=0$ the values at $n=1,2$ are $0$ and $1/4$; the display (51) under it needs increasing
--   - encoding: monotone in $n$ → comparison of consecutive $n\ge k$; reason: $k/n$ is a probability exactly for $n\ge k$; consecutive comparisons give monotonicity
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, proof of Lemma 3, p.38

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

open CommitteeVoting.SingleVoter (pbCDF)

namespace StaticProphetSec

/-- Hoeffding's monotonicity, corrected (Arnosti & Ma, arXiv:2108.12893v2, proof of Lemma 3,
p.38): for `j < k`, `P(Bin(n, k/n) ≤ j)` is increasing in `n ≥ k`.

**Formalization Note.** The page prints "decreasing in n", which is false: for `k = 1`, `j = 0`
the values at `n = 1, 2` are `0` and `1/4`. The display under it needs "increasing". -/
theorem hoeffding_monotonicity (k n j : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hj : j < k) :
    pbCDF (fun _ : Fin n => (k : ℝ) / (n : ℝ)) Finset.univ j ≤
      pbCDF (fun _ : Fin (n + 1) => (k : ℝ) / ((n + 1 : ℕ) : ℝ)) Finset.univ j := by sorry

end StaticProphetSec
