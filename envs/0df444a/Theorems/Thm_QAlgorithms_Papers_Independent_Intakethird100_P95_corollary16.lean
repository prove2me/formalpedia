-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_corollary16
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.corollary16
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:34:04.062388+00:00
-- url     : https://prove2.me/theorems/6a20d8b1-5592-404b-9e06-ee1543fda9a1
-- title:
--   Corollary 16: equality of S_oneHalf forbids nontrivial preparation
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. Assume in addition that all entries of $\lambda$ are strictly positive, so $d$ is its Schmidt rank. For a positive integer $K$, $\Phi_K$ denotes the maximally entangled state of Schmidt rank $K$. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. Let $K\ge2$ and $d\ge K$. If $S_{1/2}(\lambda)=\log_2 K$, then
--
--   $$\Phi_K\to^{\rm PPT}\rho_\lambda\quad\Longrightarrow\quad d=K\;\text{ and }\;\lambda_i=1/K\text{ for every }i.$$
--
--   Thus the entropy equality case permits only the same maximally entangled nonzero spectrum, up to local unitaries.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 7, Corollary 16: equality of S_oneHalf forbids nontrivial preparation

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

/-- PDF p.7, Corollary 16: only-if, including the entropy equality boundary.
Full support makes equality of nonzero spectra exactly d=K and uniform entries. -/
theorem corollary16 {d : ℕ} (K : ℕ) (hK : 2 ≤ K) (lam : Fin d → ℝ)
    (hprob : IsProbability lam) (hpos : ∀ i, 0 < lam i) (hd : K ≤ d)
    (hentropy : schmidtRenyi (1 / 2) lam = logTwo (K : ℝ)) :
    Reach (maximallyEntangledDensity K) (schmidtDensity lam) → d = K ∧ ∀ i, lam i = (K : ℝ)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
