-- Prove2me | Theorems.Thm_ParallelHAC_Supplement_theorem_9_packing
-- name    : ParallelHAC.Supplement.theorem_9_packing
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T00:33:06.101209+00:00
-- url     : https://prove2.me/theorems/948e7352-dd73-4e20-b27b-39bb1c88ee17
-- title:
--   Theorem 9 — $r$-separated points in a radius-$R$ ball number at most $(1+3R/r)^k\le(1+R/r)^{3k}$
-- statement:
--   Let $r>0$ and $R\ge0$, and let $P\subseteq\mathbb R^k$ be a set of points such that $\|u-v\|\ge r$ for all distinct $u,v\in P$ and $P\subseteq B(x,R)=\{y:\|y-x\|\le R\}$ for some $x\in\mathbb R^k$. Then $P$ is finite and
--   $$|P|\le\Bigl(1+\frac{3R}r\Bigr)^k\le\Bigl(1+\frac Rr\Bigr)^{3k}.$$
--
--   This folklore packing bound is the only place where low dimension enters the paper's arguments: it underlies the packability of centroid and Ward's linkage (Theorems 1 and 2).
--
--   **Formalization Note** $P$ is an arbitrary set, so finiteness is part of the conclusion; $|P|$ is `Set.ncard`.
--
--   Differences from the source:
--   - generalization: (1 + R/r)^{O(k)} → (1 + R/r)^{3k}; reason: the exponent 3k is the one the proof on p.53 gives; an explicit exponent implies the O(k) claim
--   - encoding: a collection of points P with |P| ≤ … → P : Set (EuclideanSpace ℝ (Fin k)), conclusion P.Finite ∧ (P.ncard : ℝ) ≤ …; reason: finiteness of P is a consequence, so it is concluded; ncard of a finite set is its cardinality
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §3, Theorem 9, p.14 (PDF p.17); proof App. A.1, p.53 (PDF p.56)

import Mathlib

namespace ParallelHAC.Supplement

/-- **Theorem 9** (Packing points in `ℝ^k`, folklore; p.14): let `r > 0`, `R ≥ 0`, and let
`P ⊆ ℝ^k` be a set of points with `‖u − v‖ ≥ r` for all distinct `u, v ∈ P`, contained in a closed
ball `B(x, R)`. Then `P` is finite, `|P| ≤ (1 + 3R/r)^k`, and `(1 + 3R/r)^k ≤ (1 + R/r)^{3k}`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §3, Theorem 9, printed p.14 (PDF p.17); restated
and proved in App. A.1, printed p.53 (PDF p.56).

**Formalization Note.** `ℝ^k` is `EuclideanSpace ℝ (Fin k)` and `B(x, R)` is
`Metric.closedBall x R`. `P` is any set, so finiteness is part of the conclusion. The paper's
`(1 + R/r)^{O(k)}` is stated with the exponent `3k` that its proof gives (p.53). -/
theorem theorem_9_packing (k : ℕ) (r R : ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (P : Set (EuclideanSpace ℝ (Fin k)))
    (hsep : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → r ≤ ‖u - v‖)
    (x : EuclideanSpace ℝ (Fin k)) (hx : P ⊆ Metric.closedBall x R) :
    P.Finite ∧ (P.ncard : ℝ) ≤ (1 + 3 * R / r) ^ k ∧
      (1 + 3 * R / r) ^ k ≤ (1 + R / r) ^ (3 * k) := by sorry

end ParallelHAC.Supplement
