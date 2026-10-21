-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_domain_nonattainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.finite_domain_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:08:15.952258+00:00
-- url     : https://prove2.me/theorems/cf472bdc-d2e6-40f9-9730-c10854f708d7
-- title:
--   Remark 3.14: finite-dimensional domain nuclear nonattainment
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   There exists a nuclear operator from the Euclidean plane to the Haar $L_1$ circle which fails to attain its nuclear norm, although it attains its ordinary operator norm:
--
--   $$
--   \exists T\in\mathcal N(\ell_2^2,L_1(\mathbb T)):\quad T\notin\mathrm{NA}_{\mathcal N},\quad T\in\mathrm{NA}.
--   $$
--
--   This is the negative conclusion at the end of the remark, not its preceding hypothetical argument.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 11, Remark 3.14: finite-dimensional domain nuclear nonattainment

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

/-- PDF p.11, Remark 3.14: a nuclear operator from the Euclidean plane to circle L1
fails nuclear attainment, while attaining its ordinary operator norm. -/
theorem finite_domain_nonattainment :
    ∃ T : Nuclear K (Plane K) (CircleL1 K), ¬ NuclearAttains T ∧ OperatorAttains (nuclearOperator T) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
