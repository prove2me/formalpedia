-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_proposition17
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.proposition17
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:35:24.346076+00:00
-- url     : https://prove2.me/theorems/fd1f6f6b-87ce-4100-aa4e-19d7f9d74bca
-- title:
--   Proposition 17: rank-one dual tightness for K=2 and rank three
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. Assume in addition that all entries of $\lambda$ are strictly positive, so $d$ is its Schmidt rank. For $K\ge2$, let $T(K;\lambda)$ be the minimum of the Schmidt-coordinate primal SDP (20), defined independently of operational reachability. Its real variables $s_{ij}$ for $j\le i$ and $a_{ij}$ for $j<i$ obey $s_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K+1)$ and $a_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K-1)$, and the matrix $\sum_{i\ge j}s_{ij}\sigma_{ij}^{\Gamma}+\sum_{i>j}a_{ij}\alpha_{ij}^{\Gamma}$ is positive semidefinite. The objective is $\sum s_{ij}+\sum a_{ij}$. Here $\sigma_{ii}=|ii\rangle\langle ii|$, while the off-diagonal symmetric and antisymmetric projectors are $(|ij\rangle\pm|ji\rangle)(\langle ij|\pm\langle ji|)/2$. Write $T_1(K;\lambda)$ for the supremum of the dual objective (28) over feasible coordinates whose associated matrix has rank exactly one; attainment is not assumed. For a target of Schmidt rank exactly three and an input of rank two,
--
--   $$T(2;\lambda)=T_1(2;\lambda).$$
--
--   This equates the two optimal values in the smallest nontrivial rank-increase setting.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 7, Proposition 17: rank-one dual tightness for K=2 and rank three

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

/-- PDF pp.7–8, Proposition 17: equality of optimal VALUES for Schmidt rank three.
The inconsistent witness coefficients in (42)–(45) are not asserted as lemmas. -/
theorem proposition17 (lam : Fin 3 → ℝ) (hprob : IsProbability lam)
    (hpos : ∀ i, 0 < lam i) : primalValue 2 lam = rankOneValue 2 lam := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
