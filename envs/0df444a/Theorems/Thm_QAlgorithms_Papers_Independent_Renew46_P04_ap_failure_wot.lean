-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_ap_failure_wot
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.ap_failure_wot
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:15:45.918871+00:00
-- url     : https://prove2.me/theorems/867464fc-a92e-4516-b6aa-66b36f2d49d6
-- title:
--   Lemma 5.3: AP failure and bounded finite-rank WOT closure
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If $X$ fails the approximation property, then for every $R>0$,
--
--   $$
--   \operatorname{id}_X\notin\overline{\{T\in\mathcal F(X,X):\|T\|\le R\}}^{\mathrm{WOT}}.
--   $$
--
--   The weak operator closure is expressed through finite sets of vectors and continuous dual functionals. The norm bound is essential; no assertion is made about closure of the entire finite-rank space.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 21, Lemma 5.3: AP failure and bounded finite-rank WOT closure

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

/-- PDF p.21, Lemma 5.3: the bounded ball is essential; this is not closure of all finite-rank maps. -/
theorem ap_failure_wot [CompleteSpace X] (h : ¬ ApproximationProperty K X) (R : ℝ) (hR : 0 < R) :
    ¬ InWOTClosure {T : X →L[K] X | FiniteDimensional K T.range ∧ ‖T‖ ≤ R}
      (ContinuousLinearMap.id K X) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
