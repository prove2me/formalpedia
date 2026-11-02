-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_example7
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.example7
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:27:12.860993+00:00
-- url     : https://prove2.me/theorems/36e82970-b27c-403a-bb01-28eb0d988dc5
-- title:
--   Example 7: lower-order Renyi entropies are not PPT monotones
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. Consider the specific spectrum
--
--   $$\lambda=(1,1,1,4,4,9)/20.$$
--
--   It has $S_{1/2}(\lambda)=\log_2 5$. There is an integer sequence $m(n)$ with $m(n)/n\to1$ such that $\Phi_5^{\otimes m(n)}\to^{\rm PPT}\rho_\lambda^{\otimes n}$ for every sufficiently large integer $n$. For each real $t$ with $0\le t<1/2$,
--
--   $$\log_2 5<S_t(\lambda).$$
--
--   For every such $t$ there are positive $n$ and an integer $m\ge0$ for which this exact conversion holds and the input entropy $\log_2(5^m)$ is strictly less than the output entropy $S_t(\lambda^{\otimes n})$. Thus every order in that interval fails to be a PPT monotone.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 4, Example 7: lower-order Renyi entropies are not PPT monotones

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

/-- PDF p.4, Example 7: integer n+o(n) resource copy counts, the exact asymptotic
conversion, and the strict inequality at EVERY order 0 ≤ t < 1/2. The alpha/t
mismatch and the down-arrow on an ascending list are source typographical errors. -/
theorem example7 :
    IsProbability exampleSpectrum ∧ schmidtRenyi (1 / 2) exampleSpectrum = logTwo 5 ∧
    (∃ m : ℕ → ℕ, Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop (nhds 1) ∧
      ∃ N : ℕ, ∀ n ≥ N, Reach (maximallyEntangledDensity (5 ^ m n)) (rhoPower exampleSpectrum n)) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 / 2 → logTwo 5 < schmidtRenyi t exampleSpectrum) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 / 2 →
      ∃ n m : ℕ, 0 < n ∧ Reach (maximallyEntangledDensity (5 ^ m)) (rhoPower exampleSpectrum n) ∧
        logTwo ((5 ^ m : ℕ) : ℝ) < schmidtRenyi t (tensorSpectrum exampleSpectrum n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
