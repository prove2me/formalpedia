-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_remark14
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.remark14
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:32:28.93897+00:00
-- url     : https://prove2.me/theorems/e5b84848-e0c5-469d-85c0-dcd6526a47df
-- title:
--   Remark 14: rank-one dual lower bound as a necessary condition
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. Assume in addition that all entries of $\lambda$ are strictly positive, so $d$ is its Schmidt rank. For $K\ge2$, let $T(K;\lambda)$ be the minimum of the Schmidt-coordinate primal SDP (20), defined independently of operational reachability. Its real variables $s_{ij}$ for $j\le i$ and $a_{ij}$ for $j<i$ obey $s_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K+1)$ and $a_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K-1)$, and the matrix $\sum_{i\ge j}s_{ij}\sigma_{ij}^{\Gamma}+\sum_{i>j}a_{ij}\alpha_{ij}^{\Gamma}$ is positive semidefinite. The objective is $\sum s_{ij}+\sum a_{ij}$. Here $\sigma_{ii}=|ii\rangle\langle ii|$, while the off-diagonal symmetric and antisymmetric projectors are $(|ij\rangle\pm|ji\rangle)(\langle ij|\pm\langle ji|)/2$. Write $T_1(K;\lambda)$ for the supremum of the dual objective (28) over feasible coordinates whose associated matrix has rank exactly one; attainment is not assumed. The rank-one dual objective set is nonempty and bounded above. Moreover,
--
--   $$T_1(K;\lambda)\le T(K;\lambda),\qquad\Phi_K\to^{\rm PPT}\rho_\lambda\;\Longrightarrow\;T_1(K;\lambda)\le1.$$
--
--   The restricted dual therefore gives a necessary preparation condition without assuming a rank-one maximizer.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 7, Remark 14: rank-one dual lower bound as a necessary condition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF p.7, Remark 14: restricted SUPREMUM lower bound and necessary condition.
No general rank-one optimizer is asserted; domain facts accompany the real supremum. -/
theorem remark14 {d : ℕ} (K : ℕ) (hK : 2 ≤ K) (lam : Fin d → ℝ)
    (hprob : IsProbability lam) (hpos : ∀ i, 0 < lam i) :
    (rankOneValues K lam).Nonempty ∧ BddAbove (rankOneValues K lam) ∧
    rankOneValue K lam ≤ primalValue K lam ∧
    (Reach (maximallyEntangledDensity K) (schmidtDensity lam) → rankOneValue K lam ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
