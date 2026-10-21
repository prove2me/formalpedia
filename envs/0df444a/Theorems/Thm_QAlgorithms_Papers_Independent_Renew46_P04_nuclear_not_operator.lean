-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_nuclear_not_operator
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.nuclear_not_operator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:56:42.526328+00:00
-- url     : https://prove2.me/theorems/8fda0660-9283-4466-8d20-33acd708216c
-- title:
--   Remark 3.4: nuclear versus operator attainment
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If $Y$ is infinite dimensional and strictly convex, then there is a nuclear operator from $c_0$ to $Y$ with
--
--   $$
--   T\in\mathrm{NA}_{\mathcal N}(c_0,Y),\qquad T\notin\mathrm{NA}(c_0,Y).
--   $$
--
--   This distinguishes nuclear norm attainment from ordinary operator norm attainment without a reflexivity assumption on $Y$.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 8, Remark 3.4: nuclear versus operator attainment

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

section SequenceResults

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

/-- PDF p.8, Remark 3.4: nuclear attainment need not imply operator attainment;
no reflexivity of the range is assumed. -/
theorem nuclear_not_operator (hi : ¬ FiniteDimensional K Y) (hc : StrictlyConvex Y) :
    ∃ T : Nuclear K (CZero K ℕ) Y, NuclearAttains T ∧ ¬ OperatorAttains (nuclearOperator T) := by sorry

end SequenceResults

end QAlgorithms.Papers.Independent.Renew46.P04

end
