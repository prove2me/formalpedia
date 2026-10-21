-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_pir_comparison
-- name    : QAlgorithms.Papers.Independent.Next46.P14.pir_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:15:09.650084+00:00
-- url     : https://prove2.me/theorems/684b1315-5f3d-4ea0-b012-a91d03ae2bed
-- title:
--   Comparison with the cited ordinary-PIR curve
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. Fix equal messages, $K,N\geq2$, and $\rho\geq1/(N-1)$. Define the scalar expression cited as ordinary-PIR capacity in (13) by $P(K,N)=(\sum_{i=0}^{K-1}N^{-i})^{-1}$. Then
--
--   $$P(K,N)>C_{\rm SPIR}(K,N,p,\rho),\qquad\lim_{j\to\infty}P(j,N)=C_{\rm SPIR}(K,N,p,\rho).$$
--
--   This records the paper’s comparison and limiting penalty. The operational identification of P with ordinary-PIR capacity is cited background from [3], and is not a new theorem here.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 5, Observation 4, (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Observation 4, PDF pp.5–6, with the scalar expression (13): for fixed N,
the cited PIR curve is strictly larger and converges to feasible SPIR spirCapacity
as K tends to infinity. This does not assert the operational PIR theorem of [3]. -/
theorem pir_comparison (m : SpirParameters) (hK : 2 ≤ m.K) (hN : 2 ≤ m.N)
    (hequal : ∀ k, m.ell k = 1) (rho : ℝ)
    (hrho : 1 / ((m.N : ℝ) - 1) ≤ rho) :
    spirCapacity m rho < ENNReal.ofReal (pirExpression m.K m.N) ∧
    Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (pirExpression (k + 2) m.N))
      Filter.atTop (nhds (spirCapacity m rho)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
