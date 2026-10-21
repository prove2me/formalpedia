-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_rank_nonattainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.finite_rank_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:16:46.818993+00:00
-- url     : https://prove2.me/theorems/4bcda1bb-3267-4a24-a687-15fde17ecbed
-- title:
--   Proposition 5.5: finite-rank tensor nonattainment
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   There exist real Banach spaces $X,Y$ and an algebraic tensor $u\in X\otimes Y$ whose canonical image $\iota(u)$ in the completion satisfies
--
--   $$
--   \iota(u)\notin\mathrm{NA}_\pi(X\widehat\otimes_\pi Y).
--   $$
--
--   Finite rank here means belonging to the algebraic tensor image. No finite optimal decomposition or associated finite-rank nuclear map is substituted.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 22, Proposition 5.5: finite-rank tensor nonattainment

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

/-- PDF p.22, Proposition 5.5: finite rank is membership in the algebraic tensor image,
without claiming an optimal finite decomposition or a finite-rank nuclear realization. -/
theorem finite_rank_nonattainment :
    ∃ X Y : BanachData ℝ, ∃ u : Algebraic ℝ X.Carrier Y.Carrier,
      ¬ TensorAttains (algebraicInclusion u) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
