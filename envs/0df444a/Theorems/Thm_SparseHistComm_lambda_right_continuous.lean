-- Prove2me | Theorems.Thm_SparseHistComm_lambda_right_continuous
-- name    : SparseHistComm.lambda_right_continuous
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:04.64522+00:00
-- url     : https://prove2.me/theorems/02fdb507-4509-42c5-9606-79da8d1a37fc
-- title:
--   Proof of Theorem 3 — $\Lambda_{n,k,D}$ is nonincreasing and right-continuous on $[0,1)$
-- statement:
--   Let $n \ge 1$, $k \ge 1$ and $0 \le D < k$. Then
--
--   1. $\delta \mapsto \Lambda_{n,k,D}(\delta)$ is nonincreasing on $[0,1)$;
--   2. for every $\delta \in [0,1)$ and every sequence $\delta_j \downarrow \delta$, $\Lambda_{n,k,D}(\delta_j) \to \Lambda_{n,k,D}(\delta)$, including when $\delta = 0$.
--
--   Right-continuity removes the posterior-threshold relaxation $\delta + O(1/\log d)$ from the leading coefficient in Theorem 3.
--
--   Differences from the source:
--   - encoding: Λ_{n,k,D} as a min over (L(R), p_R) → Lambda: sInf over probability laws ν of p_R on stdSimplex ℝ (Fin (k+1)); reason: objective and constraint depend only on the law of p_R; the paper's Lemma 3 shows the minimum is attained, so the value agrees
--   - encoding: Λ(δⱼ) → Λ(δ) for every sequence δⱼ ↓ δ → ContinuousWithinAt (Lambda n k D) (Set.Ici δ) δ; reason: sequential and filter right-continuity agree on ℝ
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-C (proof of Theorem 3), p.18

import Mathlib
import Definitions.Def_SparseHistComm_Lambda

namespace SparseHistComm

/-- **Proof of Theorem 3, monotonicity and right-continuity of `Λ`** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-C, p.18).
For `0 ≤ D < k`, `Λ_{n,k,D}` is nonincreasing in `δ ∈ [0, 1)`, and for every `δ ∈ [0, 1)`,
`Λ_{n,k,D}(δⱼ) → Λ_{n,k,D}(δ)` for `δⱼ ↓ δ`, including when `δ = 0`. -/
theorem lambda_right_continuous (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (D : ℝ) (hD0 : 0 ≤ D)
    (hDk : D < k) :
    AntitoneOn (Lambda n k D) (Set.Ico 0 1) ∧
    ∀ δ ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt (Lambda n k D) (Set.Ici δ) δ := by sorry

end SparseHistComm
