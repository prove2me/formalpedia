-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_interval_nonattainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.interval_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:07:12.059075+00:00
-- url     : https://prove2.me/theorems/ab207095-3f0c-4829-9333-ebae710f53f3
-- title:
--   Example 3.12(d): L1 interval factors
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For Lebesgue $L_1$ spaces on the unit interval,
--
--   $$
--   \exists z\in L_1[0,1]\widehat\otimes_\pi L_1[0,1]:\quad z\notin\mathrm{NA}_\pi.
--   $$
--
--   This is failure of universal attainment, compatible with density of attaining tensors for these same factors.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 11, Example 3.12(d): L1 interval factors

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

/-- PDF pp.10–11, Example 3.12(d): failure of universal attainment, not of tensor density. -/
theorem interval_nonattainment :
    ∃ z : Projective K (IntervalL1 K) (IntervalL1 K), ¬ TensorAttains z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
