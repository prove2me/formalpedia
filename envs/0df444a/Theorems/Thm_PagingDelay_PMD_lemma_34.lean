-- Prove2me | Theorems.Thm_PagingDelay_PMD_lemma_34
-- name    : PagingDelay.PMD.lemma_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:30.527608+00:00
-- url     : https://prove2.me/theorems/88446621-a29f-49c8-abee-5f7e4a2ba92d
-- title:
--   Lemma 34 — complete rounding-map properties
-- statement:
--   Let $k\ge1$, $\delta=1/(2k+1)$ and $x\in[\delta,1]^n$ with $\sum_i x_i\ge n-k$. Put $u_i=(1-x_i)/(1-\delta)$ and $z_i=\max\{0,2u_i-1\}$. Then
--
--   $$z\in[0,1]^n,\quad (x_i=\delta\implies z_i=1),\quad\sum_i z_i\le k.$$
--
--   The scalar map $x_i\mapsto z_i$ is nonincreasing and 3-Lipschitz throughout $[\delta,1]$. All five conclusions of the lemma are included.
--
--   Differences from the source:
--   - encoding: pages indexed by 1 through n → pages indexed by Fin n; reason: a bijective reindexing of the same finite page universe
--   - encoding: coordinatewise nonincreasing, 3-Lipschitz map on [δ,1] → AntitoneOn and LipschitzOnWith 3 on the closed interval; reason: these express the two scalar properties uniformly, rather than only at the supplied coordinates
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 34 — complete rounding-map properties, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 34 — complete rounding-map properties, p. 26. -/
theorem lemma_34 (n k : ℕ) (hk : 1 ≤ k) (x : Fin n → ℝ)
    (hx : ∀ i, delta k ≤ x i ∧ x i ≤ 1)
    (hmass : (n : ℝ) - k ≤ ∑ i, x i) :
    (∀ i, 0 ≤ roundingMap k (x i) ∧ roundingMap k (x i) ≤ 1) ∧
    (∀ i, x i = delta k → roundingMap k (x i) = 1) ∧
    (∑ i, roundingMap k (x i)) ≤ (k : ℝ) ∧
    AntitoneOn (roundingMap k) (Set.Icc (delta k) 1) ∧
    LipschitzOnWith 3 (roundingMap k) (Set.Icc (delta k) 1) := by sorry

end PagingDelay.PMD
