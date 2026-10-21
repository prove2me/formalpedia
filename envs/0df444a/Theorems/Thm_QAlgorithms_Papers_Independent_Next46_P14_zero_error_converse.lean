-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_zero_error_converse
-- name    : QAlgorithms.Papers.Independent.Next46.P14.zero_error_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:13:33.4768+00:00
-- url     : https://prove2.me/theorems/be2408c2-9cc2-4ffc-96db-95893c8a03f9
-- title:
--   Finite-block zero-error download and randomness converse
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. At any fixed positive blocklength assume $K,N\geq2$, exact privacy, and exactly zero decoding error for every request. Then, for every k,
--
--   $$N\ell_k L\leq(N-1)D,\qquad H_p(S)\geq\frac{\ell_k L}{N-1}.$$
--
--   Both inequalities apply to unequal messages and arbitrary discrete shared randomness. In particular, the entropy is not rounded or assumed integral.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 6, Observation 6; (51), (68)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Observation 6, PDF p.6, with (51) on PDF p.10 and (68) on PDF p.11:
finite-block zero-error converse for unequal message sizes. Shared spirEntropy is
unrounded and may be nonintegral (or infinite). -/
theorem zero_error_converse {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)
    (hK : 2 ≤ m.K) (hN : 2 ≤ m.N) (hprivate : Private b) (hcorrect : ZeroError b) :
    ∀ k, (m.N : ℝ) * ((m.ell k * L : ℕ) : ℝ) ≤
      ((m.N : ℝ) - 1) * (b.download : ℝ) ∧
      ENNReal.ofReal (((m.ell k * L : ℕ) : ℝ) / ((m.N : ℝ) - 1)) ≤
        spirEntropy m.p b.sharedSeed := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
