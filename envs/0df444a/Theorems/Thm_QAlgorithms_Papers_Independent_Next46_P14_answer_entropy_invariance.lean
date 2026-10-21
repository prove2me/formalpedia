-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P14_answer_entropy_invariance
-- name    : QAlgorithms.Papers.Independent.Next46.P14.answer_entropy_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:10:31.739282+00:00
-- url     : https://prove2.me/theorems/129a8d0f-2c92-484e-8368-a75dc16befe7
-- title:
--   Conditional answer-entropy invariance under a change of request
-- statement:
--   Let K and N be positive integers. Consider K independent messages replicated at N noncommunicating, noncolluding servers over the prime field $\mathbb F_p$. Message k has $\ell_k L$ independent uniform symbols, where all multipliers and L are positive integers. The user seed F, uniform requested index, messages, and shared server seed S are mutually independent. Queries depend only on F and the requested index; each server answers using only its received query, all messages, and S. User privacy compares the full server views $(Q_n,A_n,W_{1:K},S)$; database privacy requires the joint undesired-message vector to be independent of the full user view $(Q_{1:N},A_{1:N},F)$. Download D is the maximum total number of field symbols, with query-specified answer lengths; upload is not charged. The exact rate for request k is $R_k=\ell_k L/D$. Entropies use p-ary units. At a fixed positive blocklength, assume both privacy properties. For every message pair $k,k^{\prime}$, including equality, and every server n,
--
--   $$H_p(A_n^{[k]}\mid W_k,Q_n^{[k]})=H_p(A_n^{[k^{\prime}]}\mid W_k,Q_n^{[k^{\prime}]}),\qquad H_p(A_n^{[k]}\mid Q_n^{[k]})=H_p(A_n^{[k^{\prime}]}\mid Q_n^{[k^{\prime}]}).$$
--
--   These fixed-block identities require neither successful decoding nor equal message lengths. The same message $W_k$ is conditioned on in the first identity.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, PDF p. 8, Lemma 1, (25)–(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Lemma 1, PDF p.8, (25)–(26): both conditional-spirEntropy invariances.
The same W_k occurs on both sides, including the k2-request answer. -/
theorem answer_entropy_invariance {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)
    (hprivate : Private b) (k k2 : Fin m.K) (n : Fin m.N) :
    (spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => (x.1 k, b.query k x.2.1 n)) =
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k2 n)
      (fun x => (x.1 k, b.query k2 x.2.1 n))) ∧
    (spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k n)
      (fun x => b.query k x.2.1 n) =
    spirConditionalEntropy m.p (dataLaw b) (observedAnswer b k2 n)
      (fun x => b.query k2 x.2.1 n)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P14

end
