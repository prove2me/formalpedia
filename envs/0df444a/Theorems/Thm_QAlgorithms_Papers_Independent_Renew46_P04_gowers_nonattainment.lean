-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_gowers_nonattainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.gowers_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:06:48.598115+00:00
-- url     : https://prove2.me/theorems/f9ab8da5-06b9-4cb7-968d-123e058981a3
-- title:
--   Example 3.12(c): Gowers-space example
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   There is a Banach space $G$, chosen independently of the exponent, such that for every $1<p<\infty$,
--
--   $$
--   \exists z\in G\widehat\otimes_\pi\ell_p:\quad z\notin\mathrm{NA}_\pi.
--   $$
--
--   This is the existential consequence of the source’s fixed Gowers example. No predicate naming that space and no bilinear obstruction is inserted as an assumption.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 10, Example 3.12(c): Gowers-space example

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

/-- PDF p.10, Example 3.12(c): one Banach witness is chosen before every exponent p.
This is the existential consequence of the cited Gowers construction, without an opaque predicate. -/
theorem gowers_nonattainment :
    ∃ G : BanachData K, ∀ (p : ℝ≥0∞) (hp : 1 < p), p < ⊤ →
      letI : Fact (1 ≤ p) := ⟨le_of_lt hp⟩
      ∃ z : Projective K G.Carrier (lp (fun _ : ℕ => K) p), ¬ TensorAttains z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
