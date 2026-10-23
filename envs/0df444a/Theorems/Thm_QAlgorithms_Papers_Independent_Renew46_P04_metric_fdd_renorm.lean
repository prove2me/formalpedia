-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_fdd_renorm
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_fdd_renorm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:11:50.534843+00:00
-- url     : https://prove2.me/theorems/38aebe4c-bf5d-49c4-ba41-538b0afa57ac
-- title:
--   Example 4.12(a): FDDs and renorming
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   A Banach space with a finite-dimensional decomposition whose ordered partial-sum projections are contractive has the metric $\pi$ property. In addition, every Banach space $X$ with a Schauder basis admits an equivalent Banach renorming $X_{\mathrm{new}}$ satisfying
--
--   $$
--   X\simeq_{\mathrm{top.lin.}}X_{\mathrm{new}},\qquad X_{\mathrm{new}}\text{ has the metric }\pi\text{ property}.
--   $$
--
--   A Schauder expansion is a unique limit of ordered partial sums, not an unconditional sum. The zero space is permitted in the contractive FDD formulation.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 16, Example 4.12(a): FDDs and renorming

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

/-- PDF pp.16–17, Example 4.12(a): the FDD clause and its equivalent-renorming consequence.
An equivalent renorming is expressed by a topological linear isomorphism to the renormed Banach space. -/
theorem metric_fdd_renorm (X : Type) [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X] :
    (ContractiveFDD (K := K) (X := X) → MetricPi K X) ∧
    (HasSchauderBasis (K := K) (X := X) → ∃ B : BanachData K,
      Nonempty (X ≃L[K] B.Carrier) ∧ MetricPi K B.Carrier) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
