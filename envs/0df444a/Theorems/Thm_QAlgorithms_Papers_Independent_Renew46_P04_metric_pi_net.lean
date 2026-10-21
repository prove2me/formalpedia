-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_pi_net
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_pi_net
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:10:25.942931+00:00
-- url     : https://prove2.me/theorems/fb91fb9c-5175-4a28-8085-db51a3dccb3a
-- title:
--   Unnumbered p.15: metric π projection-net equivalence
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   The metric $\pi$ property means that every finite set of unit vectors can be approximated arbitrarily closely by a common finite-dimensional contractively complemented subspace. It is equivalent to a net of finite-rank contractive projections converging strongly to the identity:
--
--   $$
--   X\text{ has metric }\pi\quad\Longleftrightarrow\quad \exists(P_i):\ P_i^2=P_i,\ \|P_i\|\le1,\ \dim\operatorname{ran}P_i<\infty,\ P_ix\to x\ (x\in X).
--   $$
--
--   The canonical index is a positive tolerance in reverse order together with a finite subset of the unit sphere in inclusion order. Non-strict tolerance order repairs the printed nonreflexive relation; the zero space uses zero projections.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 15, Unnumbered p.15: metric π projection-net equivalence

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

/-- PDF p.15: metric pi is equivalent to a strongly convergent net of contractive finite-rank projections.
A genuine directed preorder replaces the printed strict, nonreflexive epsilon relation. -/
theorem metric_pi_net [CompleteSpace X] : MetricPi K X ↔
    ∃ P : (OrderDual {eps : ℝ // 0 < eps} × Finset {x : X // ‖x‖ = 1}) → (X →L[K] X),
      (∀ i, (P i).comp (P i) = P i ∧ ‖P i‖ ≤ 1 ∧ FiniteDimensional K (P i).range) ∧
      ∀ x, Tendsto (fun i => P i x) atTop (𝓝 x) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
