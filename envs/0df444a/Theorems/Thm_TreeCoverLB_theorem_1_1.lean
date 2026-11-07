-- Prove2me | Theorems.Thm_TreeCoverLB_theorem_1_1
-- name    : TreeCoverLB.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:52.575667+00:00
-- url     : https://prove2.me/theorems/7aefdcd8-a1de-48e1-9055-82105fc07d70
-- title:
--   Theorem 1.1: every size-$k$ tree cover of some $n$-point metric has distortion $\Omega_k(n^{1/(k-1)^2})$
-- statement:
--   For every integer $k\ge 3$ there are $c>0$ and $N_0$, depending only on $k$, such that for every integer $n\ge N_0$ there is an $n$-point metric space $(X,d)$ with the following property: whenever $T_1,\dots,T_k$ are edge-weighted trees on the vertex set $X$ (nonnegative weights, no Steiner points) such that every $T_i$ dominates $d$ and every pair $x,y$ satisfies $d_{T_i}(x,y)\le\alpha\,d(x,y)$ for some $i$, then
--   $$
--   \alpha\ \ge\ c\,n^{1/(k-1)^2}.
--   $$
--
--   The previous lower bound was $\Omega_k(n^{1/2^{k-1}})$; the best known upper bound is $\tilde O(n^{1/k})$.
--
--   Differences from the source:
--   - encoding: an n-point metric space; distortion at least Ω_k(n^{1/(k−1)²}) → a metric function on Fin n; ∃ c > 0, ∃ N₀ chosen after k and before n, with every cover's α ≥ c n^{1/(k−1)²}; reason: the paper's convention for subscripted asymptotics (p.8)
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 1.1, p.1 (PDF p.3); restated as Theorem 5.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_TreeCoverLB_IsFinMetric
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_TreeCoverLB_IsTreeCover

open Classical

namespace TreeCoverLB

/-- **Theorem 1.1** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Theorem 1.1, p.1 (PDF p.3); restated as Theorem 5.2, p.18 (PDF p.20)): for
every integer `k ≥ 3` and every sufficiently large integer `n`, there exists an `n`-point metric
space for which every size-`k` tree cover has distortion at least `Ω_k(n^{1/(k−1)²})`.

Explicitly: there are `c > 0` and `N₀`, depending only on `k`, such that for every `n ≥ N₀` there is a
metric `d` on `n` points such that, whenever `k` edge-weighted trees on exactly these `n` points (no
Steiner points, nonnegative weights) all dominate `d` and every pair is `α`-approximated in one of
them, `α ≥ c · n^{1/(k−1)²}`.

**Formalization Note** The `n`-point metric space is `Fin n` with a metric function (`IsFinMetric`);
a size-`k` tree cover is `T : Fin k → WeightedTree (Fin n)` with `IsTreeCover d T α`. `Ω_k` follows the
paper's convention (p.8, "A subscript in an asymptotic notation indicates that the subscripted
parameters are treated as constants"): `c` and `N₀` are chosen after `k` and before `n`. The exponent
is the real number `1/(k − 1)²`. -/
theorem theorem_1_1 (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ dist : Fin n → Fin n → ℝ, IsFinMetric dist ∧
        ∀ (T : Fin k → WeightedTree (Fin n)) (α : ℝ), IsTreeCover dist T α →
          c * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1) ^ 2) ≤ α := by sorry

end TreeCoverLB
