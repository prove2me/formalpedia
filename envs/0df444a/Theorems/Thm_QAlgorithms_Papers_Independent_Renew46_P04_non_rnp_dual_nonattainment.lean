-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_non_rnp_dual_nonattainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.non_rnp_dual_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:06:23.318573+00:00
-- url     : https://prove2.me/theorems/8495d946-39fe-4bfd-be1b-79435d16077c
-- title:
--   Example 3.12(b): strictly convex non-RNP dual
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If the continuous dual $Y^*$ is strictly convex and fails the Banach-space Radon–Nikodym property, then
--
--   $$
--   \exists z\in L_1[0,1]\widehat\otimes_\pi Y:\quad z\notin\mathrm{NA}_\pi.
--   $$
--
--   The Radon–Nikodym property quantifies over absolutely continuous vector measures of bounded variation on every finite measure space and requires an integrable Bochner density. Both geometric assumptions concern $Y^*$.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 10, Example 3.12(b): strictly convex non-RNP dual

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

/-- PDF p.10, Example 3.12(b): both strict convexity and RNP failure concern Y*, not Y. -/
theorem non_rnp_dual_nonattainment (Y : Type*) [NormedAddCommGroup Y]
    [NormedSpace K Y] [CompleteSpace Y] (hc : StrictlyConvex (Y →L[K] K))
    (hr : ¬ RadonNikodym K (Y →L[K] K)) :
    ∃ z : Projective K (IntervalL1 K) Y, ¬ TensorAttains z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
