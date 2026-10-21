-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_weakConverse
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.weakConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:48:37.63398+00:00
-- url     : https://prove2.me/theorems/fa696335-8a17-4e1b-9421-40528a3f0e38
-- title:
--   Weak converse for general commuting receivers
-- statement:
--   Fix a finite-dimensional memoryless channel with $s\ge1$ independent senders, finite nonempty alphabets, and $r\ge1$ receivers whose unital *-subalgebras $\mathcal Y_j$ commute elementwise. Define $\mathcal C$ operationally using separate sender encoders, independent uniform messages, arbitrary receiver block POVMs, and vanishing average tuple error at every receiver at all sufficiently large lengths.
--
--   Let $\mathcal O$ consist of all nonnegative rate vectors $R$ for which there are one finite probability distribution $(q_u)$ and product input laws $P^{(u)}=\bigotimes_iP_i^{(u)}$, inducing channel states $\gamma_u$ of this same fixed channel, such that
--   $$
--   \sum_{i\in J}R_i\le\sum_uq_u I_{\gamma_u}(X(J):Y_j\mid X(J^c))
--   \qquad\text{for every }J\subseteq[s]\text{ and }j\in[r].
--   $$
--   Then
--   $$
--   \mathcal C\subseteq\overline{\mathcal O}.
--   $$
--   The mixture is selected before the subset and receiver. This is a general-receiver outer bound; it asserts no reverse inclusion.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 3, Theorem 3 (Weak converse)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3 (weak converse), PDF pp.3-4: a single finite mixture must work for all
subsets and all commuting receivers. This is inclusion, with closure. -/
theorem weakConverse {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) :
    capacityRegion N ⊆ closure (mixtureRegion N) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
