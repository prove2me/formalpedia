-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_lemma10
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.lemma10
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:29:38.307013+00:00
-- url     : https://prove2.me/theorems/a733f6dd-153a-40d2-bb7c-94cafd337d0a
-- title:
--   Lemma 10: universal primal upper bound, corrected from its proof
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. Assume in addition that all entries of $\lambda$ are strictly positive, so $d$ is its Schmidt rank. For $K\ge2$, let $T(K;\lambda)$ be the minimum of the Schmidt-coordinate primal SDP (20), defined independently of operational reachability. Its real variables $s_{ij}$ for $j\le i$ and $a_{ij}$ for $j<i$ obey $s_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K+1)$ and $a_{ij}\ge\sqrt{\lambda_i\lambda_j}/(K-1)$, and the matrix $\sum_{i\ge j}s_{ij}\sigma_{ij}^{\Gamma}+\sum_{i>j}a_{ij}\alpha_{ij}^{\Gamma}$ is positive semidefinite. The objective is $\sum s_{ij}+\sum a_{ij}$. Here $\sigma_{ii}=|ii\rangle\langle ii|$, while the off-diagonal symmetric and antisymmetric projectors are $(|ij\rangle\pm|ji\rangle)(\langle ij|\pm\langle ji|)/2$. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. The proof-supported universal upper bound is
--
--   $$T(K;\lambda)\le\frac{2^{S_{1/2}(\lambda)}}{K-1}.$$
--
--   This bound controls asymptotic and catalytic preparation costs.
--
--   **Source correction.** Printed equation (25) subtracts one in the numerator. The proof explicitly gives the bound displayed here; the printed stronger bound is false for the allowed scalar spectrum $(1)$.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 6, Lemma 10: universal primal upper bound, corrected from its proof

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

/-- PDF p.6, Lemma 10, CORRECTED FROM ITS PROOF. Printed (25) has
(2^{S_{1/2}} - 1)/(K-1); the proof's final sentence gives 2^{S_{1/2}}/(K-1).
The printed stronger bound fails for d=1, lam=(1), where T=1/(K+1)>0. -/
theorem lemma10 {d : ℕ} (K : ℕ) (hK : 2 ≤ K) (lam : Fin d → ℝ)
    (hprob : IsProbability lam) (hpos : ∀ i, 0 < lam i) :
    primalValue K lam ≤ Real.rpow 2 (schmidtRenyi (1 / 2) lam) / ((K : ℝ) - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
