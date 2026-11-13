-- Prove2me | Theorems.Thm_SaglamGV_vol_ge_choose_ge
-- name    : SaglamGV.vol_ge_choose_ge
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:48.057835+00:00
-- url     : https://prove2.me/theorems/3d7baf40-2ce8-4f2d-91b1-535a985573e3
-- title:
--   $V\ge\binom nw\ge2^{nH_2(\rho)}/(n+1)$
-- statement:
--   Let $1\le w\le n$, $d=w+1$, $V=|B_d|$ and $\rho=w/n$. Then
--
--   $$
--   V\ge\binom nw\ge\frac{2^{nH_2(\rho)}}{n+1}.
--   $$
--
--   This standard estimate converts the entropy form of the Kirshner–Samorodnitsky bounds into bounds in terms of $V$.
--
--   Differences from the source:
--   - generalization: w in the regime lg n ≪ w ≤ (1/2 − ε)n → every 1 ≤ w ≤ n; reason: the estimate holds for every such w; it specializes to the paper's
--   - encoding: 2^{nH₂(ρ)} → a real power (2 : ℝ) ^ (n * H2 (w / n)); reason: Lean convention; same values
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Appendix A, p.7 (display V ≥ (n choose w) ≥ 2^{nH₂(ρ)}/(n + 1))

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SelectiveDPT_H2

namespace SaglamGV

/-- The standard binomial estimate (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), Appendix A, p.7: "The standard estimate
V ≥ (n choose w) ≥ 2^{nH_2(ρ)}/(n + 1)").

For $1 ≤ w ≤ n$, $d = w + 1$ and $ρ = w/n$: $V ≥ \binom{n}{w} ≥ 2^{nH_2(ρ)}/(n+1)$.

**Formalization Note** $H_2$ is the published `SelectiveDPT.H2` (`Real.binEntropy p / Real.log 2`, the binary entropy in bits). The power $2^{nH_2(ρ)}$ is a real power. -/
theorem vol_ge_choose_ge (n w : ℕ) (hn : 1 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) :
    (n.choose w : ℝ) ≤ vol n (w + 1) ∧
      (2 : ℝ) ^ ((n : ℝ) * SelectiveDPT.H2 ((w : ℝ) / n)) / ((n : ℝ) + 1) ≤ n.choose w := by sorry

end SaglamGV
