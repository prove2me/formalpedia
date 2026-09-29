-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
-- name    : WeierstrassProjModel.RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/2a20f2ba-8bbf-51ef-a840-451cb1579a9f
-- title:
--   Inversion in a relative group law is the negation morphism
-- statement:
--   Let $R$ be a commutative Noetherian domain and let $W$ be a Weierstrass curve over $R$ which is elliptic. Write $E \to \operatorname{Spec} R$ for the structure morphism `projModelStrCR W.toProjective` of the projective Weierstrass model, namely $\operatorname{Proj}$ of the quotient grading of the homogeneous coordinate ring followed by the map induced by $R \to$ (degree-zero part). Let $G$ be a `RelativeGroupLaw` for this morphism: data assigning to each scheme $T$ and each $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $t$-points $\{\varphi : T \to E \mid \varphi \text{ followed by the structure morphism} = t\}$, subject to associativity, both unit laws, the left inverse law, and naturality of multiplication under base change along any $\psi$ with $\psi$ followed by $t$ equal to $t'$. Assume $G$ has the zero section as unit, in the sense that for every $T$ and every $t : T \to \operatorname{Spec} R$ the underlying morphism of $G.\mathrm{one}\,t$ is $t$ followed by the underlying morphism of `kwZeroSect R W` (the section of the model cut out on the $Y$-chart). Then for every $T$, every $t : T \to \operatorname{Spec} R$ and every $t$-point $x$, the underlying morphism of $G.\mathrm{inv}\,t\,x$ equals $x$ followed by `kw_lrAddNegDiag_negMor W`, the endomorphism of the model obtained by applying `Proj.map` to the graded homomorphism `negGradedHom`.
--
--   This is the statement that on a projective Weierstrass model any functorial group law with the standard zero section has inversion given by the classical negation $[X : -Y - a_1X - a_3Z : Z]$ (Silverman, AEC III.2.3). It is used in the transport of negation along level structures, via [`WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv`](thm.html#WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_inv_val_eq_comp_negMor_of_one_eq_kwZeroSect.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.inv_val_eq_comp_negMor_of_one_eq_kwZeroSect
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (hG : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t (projModelStrCR W.toProjective)) :
    (G.inv t x).1 = x.1 ≫ kw_lrAddNegDiag_negMor W := by sorry
