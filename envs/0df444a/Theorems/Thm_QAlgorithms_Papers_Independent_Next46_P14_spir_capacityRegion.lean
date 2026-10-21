-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_spir_capacityRegion
-- name    : QAlgorithms.Papers.Independent.Next46.P14.spir_capacityRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:09:20.729544+00:00
-- url     : https://prove2.me/theorems/90f749a0-f304-479d-9eac-604f333816f4
-- title:
--   SPIR capacity region for unequal message sizes
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. For $K,N\geq2$ and $\rho\geq0$, write $m=\max_i\ell_i$. Then
--
--   $$\mathcal C=\begin{cases}\{R\in[0,\infty)^K: R_k\leq(\ell_k/m)(1-1/N)\ orall k\},&\rho\geq1/(N-1),\\\{0\},&\rho<1/(N-1).\end{cases}$$
--
--   The coordinates are simultaneous lower guarantees; this is a rectangle rather than the set of exact ratios from one common download count.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 6, Theorem 2, (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Theorem 2, PDF p.6, (15): nonnegative rectangular spirCapacity region for unequal
messages. The budget is normalized by the largest message, as in (14). -/
theorem spir_capacityRegion (m : SpirParameters) (hK : 2 ≤ m.K) (hN : 2 ≤ m.N)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    spirCapacityRegion m rho =
      if 1 / ((m.N : ℝ) - 1) ≤ rho then
        {R | ∀ k, 0 ≤ R k ∧ R k ≤
          (m.ell k : ℝ) / (largestMultiplier m : ℝ) * (1 - 1 / (m.N : ℝ))}
      else {0} := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
