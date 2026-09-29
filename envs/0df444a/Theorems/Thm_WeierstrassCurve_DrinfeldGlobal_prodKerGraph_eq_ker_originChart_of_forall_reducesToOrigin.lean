-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin
-- name    : WeierstrassCurve.DrinfeldGlobal.prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6c76056a-e220-513f-aa9a-a421c1b0260d
-- title:
--   Sections reducing to the origin cut out prodᵢ (X - zᵢ)
-- statement:
--   Let $T$ be a Noetherian local ring that is complete for the adic topology of its maximal ideal $\mathfrak m$, and let $W$ be a Weierstrass curve over $T$ with unit discriminant; write $E \to \operatorname{Spec} T$ for the structure morphism `projModelStrCR W` of the graded-quotient Proj model of $W$, and `OriginChartRing W` for the degree-zero homogeneous localisation of that graded ring away from the coordinate $Y$, the chart containing the origin, with its elements `xOverY W` and `zOverY W` given by $X$ and $Z$ over $Y$. Let $r \in \mathbb N$, let $R_0,\dots,R_{r-1}$ be sections of $E$ over the base (morphisms from the base together with the proof that each composed with `projModelStrCR W` is the identity), and let $\chi_0,\dots,\chi_{r-1}$ be ring homomorphisms `OriginChartRing W` $\to T$. Assume each pair $(R_i,\chi_i)$ satisfies `ReducesToOrigin` for the ideal $\mathfrak m$, that is: `IsOriginChartSection` holds for $R_i$ and $\chi_i$, and the two elements `originParam` $(\chi_i) = -\chi_i(X/Y)$ and `originW` $(\chi_i)$ lie in $\mathfrak m$. Let $\Phi \colon$ `OriginChartRing W` $\to T[\![X]\!]$ be a ring homomorphism which sends the image of a scalar $t \in T$ in degree zero to the constant series $C(t)$, sends `xOverY W` to $-X$, and sends `zOverY W` to $-$`W.formalW`, the formal branch of $W$ at the origin. Then the ideal sheaf data on the pullback of `projModelStrCR W` along the identity of the base given by the product over $i$ of the kernels of the graph morphisms of the $R_i$ (`prodKerGraph`) coincides with the kernel of the composite of $\operatorname{Spec}$ of the quotient map $T[\![X]\!] \to T[\![X]\!]/\bigl(\prod_i (X - C(\mathrm{originParam}(\chi_i)))\bigr)$ precomposed with $\Phi$, followed by the origin-chart immersion `originChartι W` and the canonical map `toPullbackId` into that pullback.
--
--   This is the dictionary, as in Katz–Mazur, between a sum of sections of an elliptic curve all of whose members reduce to the origin over a complete local base and the closed subscheme of the formal group cut out by the product of the linear factors $X - z(R_i)$ in the formal parameter. It is used in the comparison of global and formal Drinfeld level structures, being cited by [`WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero`](thm.html#WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.prodKerGraph_eq_ker_originChart_of_forall_reducesToOrigin
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    {r : ℕ} (R : Fin r → Section W) (χ : Fin r → (OriginChartRing W →+* T))
    (hR : ∀ i, ReducesToOrigin (R i) (χ i) (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    prodKerGraph (projModelStrCR W) (fun i => (R i).1) (fun i => (R i).2) =
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk
          (Ideal.span {∏ i, (PowerSeries.X - PowerSeries.C (originParam (χ i)))})).comp Φ)) ≫
        originChartι W ≫ toPullbackId).ker := by sorry
