-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act
-- name    : WeierstrassCurve.DrinfeldGlobal.LevelTransport.act_relabel_eq_relabel_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/21f8377d-b52b-5450-9ece-02c4c2c09711
-- title:
--   Relabelling commutes with variable-change transport of Drinfeld pairs
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$, assigning to every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta(W)$ is a unit a relative group law on the $\mathrm{Proj}$ model of $W$. Assume $\mathcal G$ is chord-and-tangent (each member admits a points-evaluation $ev$) and origin-pinned (for each such $T$, $W$, the identity section of the member law is cut out by a ring homomorphism from the origin chart ring of $W$ to $T$ killing $x/y$ and $z/y$). Fix $q : \mathbb N$ and a level transport $\mathcal T$ for $(A,\mathcal G,q)$, i.e. operations $\mathcal T.\mathrm{map}$ on $A$-algebra maps and $\mathcal T.\mathrm{act}$ on changes of Weierstrass coordinates on raw Drinfeld pairs (a curve together with two sections), functorial, compatible with one another, and preserving the level-$q$ condition; assume $\mathcal T$ satisfies `IsSectionTransport`, so that $(\mathcal T.\mathrm{act}\,C\,x).\mathrm{curve} = C \bullet x.\mathrm{curve}$ and the two sections of $\mathcal T.\mathrm{act}\,C\,x$ compose with $\mathrm{Proj}.\mathrm{map}\,\varphi$ back to those of $x$ for every graded realiser $\varphi$ of $C$, with the analogous pin for $\mathcal T.\mathrm{map}$. Assume further that graded realisers exist: for every $A$-algebra $T$, projective Weierstrass curve $W$ over $T$ and variable change $C$ there is a graded ring map $\varphi : \mathrm{projModelGradingCR}\,W \to \mathrm{projModelGradingCR}\,(C \bullet W)$ with the irrelevant ideal condition and `IsVariableChangeHom`, and for every $A$-algebra map $f : T \to T'$ and $W$ over $T$ there is such a $\varphi$ with `IsCoefficientHom`. Then for an $A$-algebra $T$, a variable change $C$ over $T$, a matrix $g \in M_2(\mathbb Z)$, a raw Drinfeld pair $x$ over $T$ with $\Delta(x.\mathrm{curve})$ a unit and with $\Delta$ of $(\mathcal T.\mathrm{act}\,C\,x).\mathrm{curve}$ a unit, transporting the $g$-relabelling of $x$ equals the $g$-relabelling of the transport of $x$, where relabelling keeps the curve and replaces the two sections by the $\mathbb Z$-linear combinations with coefficients $(g_{00},g_{10})$ and $(g_{01},g_{11})$ formed in the relevant member law of $\mathcal G$.
--
--   This is the equivariance of the $M_2(\mathbb Z)$-relabelling operation on Drinfeld level structures under the pinned change of Weierstrass coordinates: a change of coordinates is an isomorphism of models respecting the origin, hence respects the group law and $\mathbb Z$-linear combinations of sections. It is used in the construction of relabelling morphisms on the Weierstrass level moduli functors, in particular for the $\Gamma_0$- and $\Gamma_1$-type statements about relabellings of moduli points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal
open WeierstrassProjModel

theorem WeierstrassCurve.DrinfeldGlobal.LevelTransport.act_relabel_eq_relabel_act
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (T : Type) [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) (hΔ' : IsUnit (𝒯.act C x).curve.Δ) :
    𝒯.act C (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g (𝒯.act C x) hΔ' := by sorry
