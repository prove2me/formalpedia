-- Prove2me | Theorems.Thm_WeierstrassProjModel_isIntegral_selfPullback_of_isElliptic_field
-- name    : WeierstrassProjModel.isIntegral_selfPullback_of_isElliptic_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/16b4626f-ecef-5b43-bead-056d92ae7ec9
-- title:
--   Integrality of the self-fibre-product of an elliptic projective model
-- statement:
--   Let $K$ be a field and let $W$ be a Weierstrass curve over $K$ (a tuple of coefficients $a_1,a_2,a_3,a_4,a_6$) which is elliptic, i.e. satisfies `W.IsElliptic`. Write $V = W$`.toProjective` for the associated projective Weierstrass cubic, and let $\pi =$ `projModelStrCR` $V$ be its structure morphism: the graded ring in play is the quotient grading induced on $\mathrm{MvPolynomial}(\mathrm{Fin}\,3, K)$ modulo the homogeneous ideal attached to $V$ by the grading by homogeneous submodules, and $\pi$ is the canonical map $\mathrm{Proj}$ of this graded ring to $\mathrm{Spec}$ of the degree-zero part, composed with the map $\mathrm{Spec}$ of the structure morphism $K \to (\text{degree-}0\ \text{part})$, so that $\pi \colon \mathrm{Proj} \to \operatorname{Spec} K$. The assertion is that the fibre product of $\pi$ with itself, i.e. the scheme-theoretic pullback of $\pi$ along $\pi$, is an integral scheme: its underlying space is irreducible and nonempty and it is reduced.
--
--   This is the statement that $E \times_{\operatorname{Spec} K} E$ is integral for $E$ the projective model of an elliptic curve over a field, the case of the product of geometrically integral schemes over a field. It is used by [`WeierstrassProjModel.exists_dominant_field_point_selfPullback_of_isElliptic`](thm.html#WeierstrassProjModel.exists_dominant_field_point_selfPullback_of_isElliptic), where a dominant point of the self-product is produced, in the chain leading to commutativity of the group law on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_isIntegral_selfPullback_of_isElliptic_field.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.isIntegral_selfPullback_of_isElliptic_field
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    IsIntegral
      ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) := by sorry
