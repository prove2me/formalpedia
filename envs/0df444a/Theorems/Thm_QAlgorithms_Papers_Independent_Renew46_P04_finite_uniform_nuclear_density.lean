-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_uniform_nuclear_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.finite_uniform_nuclear_density
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:09:11.267902+00:00
-- url     : https://prove2.me/theorems/21afa29b-2f1a-494e-9139-a22f972f63cb
-- title:
--   Corollary 4.4: finite-dimensional domain, uniformly convex range
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If $X$ is finite dimensional and $Y$ is uniformly convex, then
--
--   $$
--   \overline{\mathrm{NA}_{\mathcal N}(X,Y)}^{\|\cdot\|_N}=\mathcal N(X,Y).
--   $$
--
--   This is nuclear-norm density under the stated geometric assumptions, without an additional approximation-property hypothesis.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 12, Corollary 4.4: finite-dimensional domain, uniformly convex range

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

/-- PDF p.12, Corollary 4.4: finite-dimensional domain and uniformly convex range. -/
theorem finite_uniform_nuclear_density [FiniteDimensional K X] [UniformConvexSpace Y] :
    NuclearDense K X Y := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
