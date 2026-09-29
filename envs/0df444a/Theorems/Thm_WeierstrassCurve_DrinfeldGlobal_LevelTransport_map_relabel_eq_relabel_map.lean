-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
-- name    : WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_relabel_eq_relabel_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/066941dd-6687-548f-b241-f697db225eac
-- title:
--   Base change commutes with GL₂(ℤ)-relabelling of raw Drinfeld pairs
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of group laws over $A$, assigning to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant a relative group law on the structure morphism of the projective model of $W$. Assume $\mathcal{G}$ is chord–tangent (for all such $T$, $W$, $\Delta$ invertible there is an evaluation witnessing `IsPointsEval` for $\mathcal{G}\,T\,W$) and has origin identity (the identity section of each $\mathcal{G}\,T\,W$ is cut out by a ring homomorphism $\chi$ from the origin chart ring to $T$ killing $x/y$ and $z/y$). Let $q$ be a natural number and $\mathcal{T}$ a level transport for $A$, $\mathcal{G}$, $q$, i.e. functorial base-change and variable-change operations on raw Drinfeld pairs preserving the level-$q$ condition, and assume $\mathcal{T}$ satisfies the section-transport condition: the curve of $\mathcal{T}.\mathrm{act}\,C\,x$ is $C \bullet x.\mathrm{curve}$ and that of $\mathcal{T}.\mathrm{map}\,f\,x$ is $x.\mathrm{curve}$ base-changed along $f$, and in each case the two sections compose with $\mathrm{Proj}$ of any realising graded homomorphism (variable-change, resp. coefficient) to give back, resp. to give the base change of, the original sections. Assume further that realisers exist: for every $A$-algebra $T$, curve $W$ and variable change $C$ there is a graded ring homomorphism from the graded model ring of $W$ to that of $C \bullet W$ satisfying `IsVariableChangeHom`, whose image dominates the irrelevant ideal; and likewise, for every $A$-algebra homomorphism $f : T \to T'$ and curve $W$ over $T$, a graded homomorphism to the model ring of $W$ base-changed along $f$ satisfying `IsCoefficientHom`, with the same irrelevant-ideal condition. Then for $A$-algebras $T$, $T'$, an $A$-algebra homomorphism $f : T \to T'$, an integer $2 \times 2$ matrix $g$, a raw Drinfeld pair $x = (W, P, Q)$ over $T$ with $\Delta(W)$ a unit, and a proof that the discriminant of the curve of $\mathcal{T}.\mathrm{map}\,f\,x$ is a unit, applying $\mathcal{T}.\mathrm{map}\,f$ to the relabelled pair $(W,\ g_{00}P + g_{10}Q,\ g_{01}P + g_{11}Q)$, where the integer combinations are formed in the group law $\mathcal{G}\,T\,W$, gives the same raw Drinfeld pair as relabelling $\mathcal{T}.\mathrm{map}\,f\,x$ by $g$ using the group law on the base-changed curve.
--
--   This is the naturality of the right $M_2(\mathbb{Z})$-relabelling action on raw Drinfeld pairs with respect to base change of the coefficient ring, reflecting that base change of sections is a homomorphism of the associated group schemes. It is used throughout the treatment of full-level and $\Gamma_0$-type level structures on moduli of elliptic curves, for instance in the determination of determinants from the kernels of classifying maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map.lean

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

open CategoryTheory AlgebraicGeometry WeierstrassProjModel
open WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_relabel_eq_relabel_map
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
    (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (g : Matrix (Fin 2) (Fin 2) ℤ) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) (hΔ' : IsUnit (𝒯.map f x).curve.Δ) :
    𝒯.map f (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g (𝒯.map f x) hΔ' := by sorry
