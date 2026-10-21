-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_spir_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P14.spir_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:08:48.833686+00:00
-- url     : https://prove2.me/theorems/8742aaaf-c696-4508-8779-4678ad196eba
-- title:
--   SPIR capacity and common-randomness threshold
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. Assume $K,N\geq2$, $\ell_k=1$ for all k, and $\rho\geq0$. The operational scalar capacity is
--
--   $$C_{\rm SPIR}=\begin{cases}1-1/N,&\rho\geq1/(N-1),\\0,&\rho<1/(N-1).\end{cases}$$
--
--   This characterizes both the optimal download rate and its randomness threshold; the zero branch does not assert the existence of a reliable scheme.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 5, Theorem 1, (12)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Abstract, PDF p.1, pinned to Theorem 1, PDF p.5, (12): SPIR spirCapacity
with an available normalized randomness budget, including the zero branch. -/
theorem spir_capacity (m : SpirParameters) (hK : 2 ≤ m.K) (hN : 2 ≤ m.N)
    (hequal : ∀ k, m.ell k = 1) (rho : ℝ) (hrho : 0 ≤ rho) :
    spirCapacity m rho = ENNReal.ofReal
      (if 1 / ((m.N : ℝ) - 1) ≤ rho then 1 - 1 / (m.N : ℝ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
