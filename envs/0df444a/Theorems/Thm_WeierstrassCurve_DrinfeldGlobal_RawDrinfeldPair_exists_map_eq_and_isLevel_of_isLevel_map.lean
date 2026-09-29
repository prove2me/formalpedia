-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_exists_map_eq_and_isLevel_of_isLevel_map
-- name    : WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/ee1a8b2d-a16f-5c30-86dc-6c8a8648fae1
-- title:
--   Drinfeld q-bases lift from K to a DVR R₀
-- statement:
--   Fix a commutative ring $A$ and a prime $q$. Let $\mathcal G$ be a family of relative group laws assigning to each $A$-algebra $T$ and each projective Weierstrass curve $W$ over $T$ with unit discriminant a relative group law on the projective model of $W$; assume $\mathcal G$ is chord–tangent (each such group law admits a points-evaluation datum) and satisfies the origin-identity condition (the unit section is cut out by a ring homomorphism from the origin chart killing $x/y$ and $z/y$). Let $\mathcal T$ be a level transport datum for $(\mathcal G,q)$, i.e. functorial base-change and variable-change operations on raw Drinfeld pairs (a projective Weierstrass curve together with two sections) preserving the level-$q$ condition, and assume $\mathcal T$ is a section transport: the sections of a transported pair pull back along the induced map of projective models to the original sections. Assume further that for every $A$-algebra homomorphism $f : T \to T'$ and every projective Weierstrass curve $W/T$ there is a graded ring homomorphism $\varphi$ from the graded coordinate ring of $W$ to that of $W.\mathrm{map}\,f$, with the irrelevant ideal of the target contained in the image of the irrelevant ideal, which is a coefficient homomorphism (sending the constant $a$ to $f(a)$ and fixing the three coordinates). Let $K$ be a field that is an $A$-algebra, and $R_0$ a discrete valuation domain, an $A$-algebra with $K$ as fraction field compatibly over $A$. Let $W_0$ be a Weierstrass curve over $R_0$ with $W_0.\Delta$ a unit, and let $z'$ be a raw Drinfeld pair over $K$ whose curve equals the base change of $W_0$ to $K$ and whose two sections form a Drinfeld basis of level $q$ for the group law attached to that curve. Then there is a raw Drinfeld pair $z_0$ over $R_0$ with $\mathcal T$-transport along $R_0 \to K$ equal to $z'$, whose curve is $W_0$ and whose sections form a Drinfeld basis of level $q$ for the group law attached to $W_0$.
--
--   This is the extension statement for full level-$q$ Drinfeld structures over a discrete valuation ring with good reduction: a Drinfeld $\Gamma(q)$-basis on the generic fibre of a Weierstrass model with unit discriminant descends to the model itself. It feeds the surjectivity arguments for the level-$q$ moduli problem over discrete valuation rings used in [`ModularCurve.FullLevel.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow) and its $H_1$ variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_exists_map_eq_and_isLevel_of_isLevel_map.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map
    (A : Type u) [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (K : Type u) [Field K] [Algebra A K]
    (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra A R₀] [Algebra R₀ K]
    [IsScalarTower A R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (hΔ₀ : IsUnit W₀.Δ)
    (z' : RawDrinfeldPair K)
    (hz' : RawDrinfeldPair.IsLevel 𝒢 q (W₀.map (IsScalarTower.toAlgHom A R₀ K).toRingHom) z') :
    ∃ z₀ : RawDrinfeldPair R₀, 𝒯.map (IsScalarTower.toAlgHom A R₀ K) z₀ = z' ∧ RawDrinfeldPair.IsLevel 𝒢 q W₀ z₀ := by sorry
