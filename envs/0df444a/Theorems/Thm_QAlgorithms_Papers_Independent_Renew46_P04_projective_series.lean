-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_series
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.projective_series
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:46:39.432988+00:00
-- url     : https://prove2.me/theorems/7b0226a2-7d70-4d60-8a03-328546024e1d
-- title:
--   §2.2: projective completion and countable cost formula
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   The finite-decomposition projective seminorm on the algebraic tensor product separates points. Its Hausdorff completion is $P(X,Y)$, and the algebraic inclusion is injective, norm preserving and dense. If $C(z)$ denotes the costs of all admissible bounded countable representations of $z$, then $C(z)$ is nonempty and bounded below, and
--
--   $$
--   \|z\|_\pi=\inf C(z),\qquad \forall\varepsilon>0\ \exists c\in C(z):\ c<\|z\|_\pi+\varepsilon.
--   $$
--
--   For nonzero factors the same infimum is obtained from unit factors and absolutely summable scalar coefficients, with cost $\sum_n|a_n|$. This supplies the completed space without assuming an optimal representation.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 3, §2.2: projective completion and countable cost formula

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

/-- PDF p.3, §2.2: completion, density, and both countable infimum formulas.
The printed normalized formula does not exclude zero factors. It is restricted
to nonzero factors because their unit spheres must be nonempty; the unnormalized
formula still includes zero factors, represented by zero sequences. -/
theorem projective_series [CompleteSpace X] [CompleteSpace Y] :
    (∀ u : Algebraic K X Y, ‖u‖ = 0 ↔ u = 0) ∧
    (∀ u : Algebraic K X Y, (finiteCosts u).Nonempty ∧ BddBelow (finiteCosts u) ∧
      ‖u‖ = sInf (finiteCosts u)) ∧
    Function.Injective (algebraicInclusion : Algebraic K X Y →L[K] Projective K X Y) ∧
    DenseRange (algebraicInclusion : Algebraic K X Y →L[K] Projective K X Y) ∧
    (∀ u : Algebraic K X Y, ‖algebraicInclusion u‖ = ‖u‖) ∧
    (∀ z : Projective K X Y, (tensorCosts z).Nonempty ∧ BddBelow (tensorCosts z) ∧
      ‖z‖ = sInf (tensorCosts z) ∧
      ∀ eps : ℝ, 0 < eps → ∃ r ∈ tensorCosts z, r < ‖z‖ + eps) ∧
    (Nontrivial X → Nontrivial Y → ∀ z : Projective K X Y,
      (normalizedCosts z).Nonempty ∧ BddBelow (normalizedCosts z) ∧
      ‖z‖ = sInf (normalizedCosts z)) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
