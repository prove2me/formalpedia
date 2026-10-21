-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_crossnorm_ball
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.projective_crossnorm_ball
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:48:05.190407+00:00
-- url     : https://prove2.me/theorems/93377555-c4e7-4b7a-9905-66a7fde19df6
-- title:
--   §2.2: pure-tensor norm and unit ball
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Let $B_E$ denote the closed unit ball of a normed space $E$. Then
--
--   $$
--   \|x\otimes y\|_\pi=\|x\|\|y\|,\qquad B_{P(X,Y)}=\overline{\operatorname{co}}\{x\otimes y:x\in B_X,\ y\in B_Y\}.
--   $$
--
--   The convex hull is taken over real scalars, also for complex spaces. These identities characterize the pure tensors and the entire closed projective unit ball.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 3, §2.2: pure-tensor norm and unit ball

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

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- PDF p.3, §2.2: crossnorm equality and the closed convex unit ball.
Convexity is over the real scalars also in the complex case. -/
theorem projective_crossnorm_ball [CompleteSpace X] [CompleteSpace Y] :
    letI := NormedSpace.restrictScalars ℝ K (Projective K X Y)
    (∀ (x : X) (y : Y), ‖pure (K := K) x y‖ = ‖x‖ * ‖y‖) ∧
    Metric.closedBall (0 : Projective K X Y) 1 =
      closure (convexHull ℝ {z | ∃ (x : X) (y : Y),
        ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ z = pure x y}) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
