-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_single_message_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P14.single_message_capacity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:11:54.821101+00:00
-- url     : https://prove2.me/theorems/aaaff99c-678c-4578-ab7f-a13db4ba3385
-- title:
--   One-message SPIR has capacity one
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. If $K=1$, $N\geq1$, the single multiplier is any positive integer, and $\rho\geq0$, then
--
--   $$C_{\rm SPIR}=1,\qquad\mathcal C=\{R\in[0,\infty)^1:R_1\leq1\}.$$
--
--   The undesired-message vector is empty, so database privacy is automatic. This boundary includes a single server and zero available common randomness.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 4, §§3.1–3.2, one-message boundary (PDF pp.4,6)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Sections 3.1–3.2, PDF pp.4,6: K=1 has capacity one and its
nonnegative lower-rate region is [0,1]. The Section 3.2 boundary allows
any positive multiplier, N=1, and zero available common randomness. -/
theorem single_message_capacity (m : SpirParameters) (hK : m.K = 1)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    spirCapacity m rho = 1 ∧
      spirCapacityRegion m rho = {R | ∀ k, 0 ≤ R k ∧ R k ≤ 1} := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
