-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv
-- name    : WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/4e674dc0-aead-5f35-a578-caeaa1c1c08c
-- title:
--   Negation variable change transports to group-law inversion
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$: for every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with unit discriminant, a relative group law on the projective model of $W$. Assume $\mathcal G$ is chord–tangent (each $\mathcal G\,T\,W\,h_\Delta$ admits a points-evaluation datum) and origin-pinned (each admits a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ which is an origin-chart section of the unit $\mathcal G\,T\,W\,h_\Delta$ applied to the identity, with $\chi(x/y)=\chi(z/y)=0$). Let $q$ be a natural number and $\mathcal T$ a level transport for $(A,\mathcal G,q)$, i.e. functorial operations on raw Drinfeld pairs along $A$-algebra maps and along Weierstrass variable changes, compatible with composition and preserving the level-$q$ condition; assume $\mathcal T$ satisfies the section-transport condition, which expresses both operations on the underlying sections through $\mathrm{Proj}$ of graded realisers. Assume further that for every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every variable change $C$ there is a graded homomorphism $\varphi$ from the graded ring of $W$ to that of $C\bullet W$, satisfying the containment of irrelevant ideals needed to induce a morphism of $\mathrm{Proj}$'s, and realising $C$ in coordinates: $\varphi$ fixes constants, $X_0\mapsto u^2X_0+rX_2$, $X_1\mapsto u^3X_1+u^2sX_0+tX_2$, $X_2\mapsto X_2$. Finally let $K$ be a field which is an $A$-algebra, $x=(W,P,Q)$ a raw Drinfeld pair over $K$, and assume $\Delta_W$ is a unit. Then the curve of $\mathcal T.\mathrm{act}\,(-1,0,-a_1,-a_3)\,x$ equals $W$, and under the resulting identification of projective models the underlying morphisms of the two transported sections are, respectively, the underlying morphisms of the $\mathcal G$-inverses of $P$ and of $Q$ over the identity base.
--
--   This identifies the level transport along the negation variable change $(-1,0,-a_1,-a_3)$ of a Weierstrass curve with inversion for the pinned group law, on both sections of a Drinfeld pair over a field. It is used in the comparison of automorphisms of level structures with automorphisms of the underlying elliptic curve, and in [`WeierstrassCurve.DrinfeldGlobal.map_eq_of_act_relabel_eq`](thm.html#WeierstrassCurve.DrinfeldGlobal.map_eq_of_act_relabel_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_exists_act_neg_comp_eqToHom_eq_inv.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem WeierstrassCurve.DrinfeldGlobal.LevelTransport.exists_act_neg_comp_eqToHom_eq_inv
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (K : Type) [Field K] [Algebra A K] (x : RawDrinfeldPair K) (hΔ : IsUnit x.curve.Δ) :
    ∃ hc : (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).curve = x.curve,
      (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).P.1 ≫ eqToHom (congrArg projModelCR hc) =
          ((𝒢 K x.curve hΔ).inv (𝟙 _) x.P).1 ∧
        (𝒯.act ⟨-1, 0, -x.curve.a₁, -x.curve.a₃⟩ x).Q.1 ≫ eqToHom (congrArg projModelCR hc) =
          ((𝒢 K x.curve hΔ).inv (𝟙 _) x.Q).1 := by sorry
