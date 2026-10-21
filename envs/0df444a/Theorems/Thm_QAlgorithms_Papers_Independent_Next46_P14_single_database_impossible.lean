-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_single_database_impossible
-- name    : QAlgorithms.Papers.Independent.Next46.P14.single_database_impossible
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:12:19.242828+00:00
-- url     : https://prove2.me/theorems/dd931dd8-2f4e-4660-b383-1c2d6ac3f59b
-- title:
--   One-server SPIR is infeasible for two or more messages
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. The available entropy budget is $H_p(S)\leq\rho L\max_i\ell_i$, with unused randomness allowed. Operational sequences have growing admissible blocklengths, exact privacy at every blocklength, and decoding error tending to zero for each request. The capacity region is the closure of simultaneous nonnegative lower rate guarantees, adjoining the zero vector in infeasible cases. For $N=1$, $K\geq2$, arbitrary positive multipliers, and any $\rho\geq0$,
--
--   $$\text{there is no asymptotically reliable exact-private protocol sequence},\qquad\mathcal C=\{0\},\qquad C_{\rm SPIR}=0.$$
--
--   The impossibility allows unlimited independent server randomness and concerns reliable schemes, rather than intentionally incorrect private protocols.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 5, §3.1, one-database boundary

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Section 3.1, PDF p.5 (repeated PDF p.6): N=1 and K≥2 admit no
asymptotically reliable exact-private sequence, even with unlimited independent
common randomness; the operational zero-spirCapacity convention is also stated. -/
theorem single_database_impossible (m : SpirParameters) (hK : 2 ≤ m.K) (hN : m.N = 1)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    IsEmpty (ReliableSequence m) ∧ spirCapacityRegion m rho = {0} ∧ spirCapacity m rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
