-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_convex_weakstar_nondensity
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.convex_weakstar_nondensity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:17:09.064596+00:00
-- url     : https://prove2.me/theorems/a13cbcc1-8ffa-42c5-8369-4937befb76d4
-- title:
--   Corollary 5.6: convexified weak-star non-density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   There exist real Banach spaces $X,Y$ with $X$ nonzero such that, for the projective predual $P(X,Y^*)$,
--
--   $$
--   \overline{\operatorname{co}\bigl(\mathrm{NA}(X,Y^{**})\cap B_{\mathcal L(X,Y^{**})}\bigr)}^{\,w^*}\ne B_{\mathcal L(X,Y^{**})}.
--   $$
--
--   The real convex hull, weak-star closure, double-dual target and unit-ball intersection are all retained.
--
--   The existential domain $X$ is required to be nonzero, excluding an empty-sphere witness; the source constructs an AP-failing, hence nonzero, domain.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 23, Corollary 5.6: convexified weak-star non-density

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

/-- PDF p.23, Corollary 5.6: weak-star closure of the convexified attaining unit ball
in operators into the double dual is a proper subset of the full unit ball.
The printed existential does not exclude X=0. We require nonzero X because its
unit sphere is otherwise empty and the inequality is trivial; the source's
AP-failing witness from Theorem 5.1 is nonzero. -/
theorem convex_weakstar_nondensity :
    ∃ X Y : BanachData ℝ, Nontrivial X.Carrier ∧
      {T : X.Carrier →L[ℝ] ((Y.Carrier →L[ℝ] ℝ) →L[ℝ] ℝ) |
        InTensorWeakStarClosure
          (convexHull ℝ {S | OperatorAttains S ∧ ‖S‖ ≤ 1}) T} ≠
        {T : X.Carrier →L[ℝ] ((Y.Carrier →L[ℝ] ℝ) →L[ℝ] ℝ) |
          ContinuousLinearMap.opNorm (σ₁₂ := RingHom.id ℝ)
            (E := X.Carrier) (F := ((Y.Carrier →L[ℝ] ℝ) →L[ℝ] ℝ)) T ≤ 1} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
