-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_nuclear_realization
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.nuclear_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:50:45.247407+00:00
-- url     : https://prove2.me/theorems/29d1bafe-e05c-4451-bd44-7a6c6d0af4e7
-- title:
--   §2.2: canonical J and full convergent-series range
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   The computed continuous extension $J$ is contractive, is uniquely determined by its rank-one values, and has exactly the operators admitting bounded absolutely norm-summable nuclear series as its range:
--
--   $$
--   \|J\|\le1,\quad J(f\otimes y)(x)=f(x)y,\quad T\in\operatorname{ran}J\iff T(x)=\sum_nf_n(x)y_n\ \text{with }\sum_n\|f_n\|\|y_n\|<\infty.
--   $$
--
--   Every displayed operator series is required to converge for every $x$. Tensor series are carried to these pointwise convergent series. The unrestricted printed equality $\|J\|=1$ is excluded as requested, since a zero factor gives $J=0$.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 4, §2.2: canonical J and full convergent-series range

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

/-- PDF p.4: the canonical J is contractive with its full convergent-series range.
The printed unqualified norm-one claim is deferred: J=0 if either factor is zero. -/
theorem nuclear_realization [CompleteSpace X] :
    ‖(projectiveRealization : Projective K (X →L[K] K) Y →L[K] (X →L[K] Y))‖ ≤ 1 ∧
    (∀ (f : X →L[K] K) (y : Y) x, projectiveRealization (pure f y) x = f x • y) ∧
    (∀ L : Projective K (X →L[K] K) Y →L[K] (X →L[K] Y),
      (∀ f y x, L (pure f y) x = f x • y) → L = projectiveRealization) ∧
    (∀ T : X →L[K] Y, T ∈ NuclearRange ↔ ∃ f y, NuclearRep T f y) ∧
    (∀ (z : Projective K (X →L[K] K) Y) (f : ℕ → (X →L[K] K)) (y : ℕ → Y),
      TensorRep z f y → ∀ x, HasSum (fun n => (f n x) • y n) (projectiveRealization z x)) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
