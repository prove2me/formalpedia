-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_corollary15
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.corollary15
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:33:17.400469+00:00
-- url     : https://prove2.me/theorems/12998ceb-c20c-4ce4-8499-404a36f3c163
-- title:
--   Corollary 15: equality in the extremal-face regime
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. Assume in addition that all entries of $\lambda$ are strictly positive, so $d$ is its Schmidt rank. For $K\ge2$, let $T(K;\lambda)$ be the minimum of the Schmidt-coordinate primal SDP (20), defined independently of operational reachability. Its real variables $s_{ij}$ for $j\le i$ and $a_{ij}$ for $j<i$ obey $s_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K+1)$ and $a_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K-1)$, and the matrix $\sum_{i\ge j}s_{ij}\sigma_{ij}^{\Gamma}+\sum_{i>j}a_{ij}\alpha_{ij}^{\Gamma}$ is positive semidefinite. The objective is $\sum s_{ij}+\sum a_{ij}$. Here $\sigma_{ii}=|ii\rangle\langle ii|$, while the off-diagonal symmetric and antisymmetric projectors are $(|ij\rangle\pm|ji\rangle)(\langle ij|\pm\langle ji|)/2$. Write $T_1(K;\lambda)$ for the supremum of the dual objective (28) over feasible coordinates whose associated matrix has rank exactly one; attainment is not assumed. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. Arrange the probabilities in nondecreasing order. If
--
--   $$\frac{\sum_{i=1}^{d-1}\sqrt{\lambda_i^\uparrow}}{K-1}>\sqrt{\lambda_d^\uparrow},$$
--
--   then
--
--   $$T(K;\lambda)=T_1(K;\lambda)=\frac{2^{S_{1/2}(\lambda)}-1}{K-1}.$$
--
--   This identifies an extremal-face regime where the rank-one lower bound is tight.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 7, Corollary 15: equality in the extremal-face regime

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

/-- PDF p.7, Corollary 15: strict extremal-face regime, sum stopping before the
largest entry. Printed proof refers to nonexistent Lemma 25 and the erroneous
strong universal bound (25); the statement is retained, with that dependency flagged. -/
theorem corollary15 {d : ℕ} (K : ℕ) (hK : 2 ≤ K) (lam : Fin (d + 1) → ℝ)
    (hprob : IsProbability lam) (hpos : ∀ i, 0 < lam i) (hsorted : Monotone lam)
    (hregime : (∑ i : Fin (d + 1), if i.val < d then Real.sqrt (lam i) else 0) /
      ((K : ℝ) - 1) > Real.sqrt (lam (Fin.last d))) :
    primalValue K lam = rankOneValue K lam ∧
      rankOneValue K lam = (Real.rpow 2 (schmidtRenyi (1 / 2) lam) - 1) / ((K : ℝ) - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
