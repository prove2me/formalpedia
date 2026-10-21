-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_user_randomness_conditional_entropy
-- name    : QAlgorithms.Papers.Independent.Next46.P14.user_randomness_conditional_entropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:11:14.820103+00:00
-- url     : https://prove2.me/theorems/9f663878-db85-4ca6-9be6-91e18f7a9661
-- title:
--   User randomness adds no conditional answer information
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. At any fixed positive blocklength with exact privacy, for every requested message k and server n,
--
--   $$H_p(A_n^{[k]}\mid W_k,F,Q_n^{[k]})=H_p(A_n^{[k]}\mid W_k,Q_n^{[k]}).$$
--
--   This is conditional irrelevance of F given the desired message and the local query; no correctness or equal-length assumption is imposed.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 9, Lemma 2, (29)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Lemma 2, PDF p.9, (29): adding private user randomness to (W_k,Q_n)
does not change answer spirEntropy. No decoding or asymptotic hypothesis. -/
theorem user_randomness_conditional_entropy {m : SpirParameters} {L : ℕ}
    (b : SpirProtocol m L) (hprivate : Private b) (k : Fin m.K) (n : Fin m.N) :
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => (x.1 k, x.2.1, b.query k x.2.1 n)) =
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => (x.1 k, b.query k x.2.1 n)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
