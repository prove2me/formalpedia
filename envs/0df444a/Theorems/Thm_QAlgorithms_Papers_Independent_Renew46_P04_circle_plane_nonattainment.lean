-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_circle_plane_nonattainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.circle_plane_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:05:48.823536+00:00
-- url     : https://prove2.me/theorems/c8a55265-d996-43d6-9587-f8f88dfa3dec
-- title:
--   Example 3.12(a): L1 circle and Euclidean plane
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Let $X=L_1(\mathbb T,m)$ for Haar measure $m$ and let $Y=\ell_2^2$ with its Euclidean norm. Then
--
--   $$
--   \exists z\in X\widehat\otimes_\pi Y:\quad z\notin\mathrm{NA}_\pi.
--   $$
--
--   The additive unit circle $\mathbb R/\mathbb Z$ supplies the Haar model. This retains the specified norms rather than an arbitrary two-dimensional factor.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 10, Example 3.12(a): L1 circle and Euclidean plane

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

/-- PDF p.10, Example 3.12(a): the specified Haar L1 space and Euclidean plane. -/
theorem circle_plane_nonattainment :
    ∃ z : Projective K (CircleL1 K) (Plane K), ¬ TensorAttains z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
