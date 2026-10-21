-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_optimal_normalized_download
-- name    : QAlgorithms.Papers.Independent.Next46.P14.optimal_normalized_download
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:14:08.913591+00:00
-- url     : https://prove2.me/theorems/787923b1-477c-46ac-a884-9b8cf3891d1f
-- title:
--   Minimum normalized SPIR download with attainment
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. Assume $K,N\geq2$ and $\rho\geq1/(N-1)$. The operational minimum cost is
--
--   $$\inf D/L=\left(\max_i\ell_i\right)\frac{N}{N-1}=:c.$$
--
--   The asymptotic cost guarantee c is achievable. There is also an exact-private, zero-error block at $L=N-1$ with $D=(\max_i\ell_i)N$ and $H_p(S)=\max_i\ell_i$, within the available budget. Its positive optimal rates satisfy $\ell_k/R_k=c$ for every k.
--
--   This records attainment in addition to the value of the operational infimum.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 6, Remark after Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Remark after Theorem 2, PDF p.6, and the p.11 construction: minimum normalized
download, with asymptotic attainment and an exact zero-error attaining block at
L=N−1. The optimal coordinate used in ell_k/R_k is positive.
Printed (72)–(73) use k where the layer must be i, and (75) has ell_k L in
an intermediate denominator instead of ell_K L; (14), (70)–(71), (74) and the
telescoping sum determine the quantities below. No printed typo is a hypothesis. -/
theorem optimal_normalized_download (m : SpirParameters) (hK : 2 ≤ m.K) (hN : 2 ≤ m.N)
    (rho : ℝ) (hrho : 1 / ((m.N : ℝ) - 1) ≤ rho) :
    let c : ℝ := (largestMultiplier m : ℝ) * (m.N : ℝ) / ((m.N : ℝ) - 1)
    minimumNormalizedDownload m rho = ENNReal.ofReal c ∧ CostAchievable m rho c ∧
    ∃ b : SpirProtocol m (m.N - 1), Private b ∧ ZeroError b ∧ WithinBudget b rho ∧
      b.download = largestMultiplier m * m.N ∧
      spirEntropy m.p b.sharedSeed = (largestMultiplier m : ℝ≥0∞) ∧
      (b.download : ℝ) / ((m.N - 1 : ℕ) : ℝ) = c ∧
      ∀ k, 0 < spirRate b k ∧ (m.ell k : ℝ) / spirRate b k = c := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
