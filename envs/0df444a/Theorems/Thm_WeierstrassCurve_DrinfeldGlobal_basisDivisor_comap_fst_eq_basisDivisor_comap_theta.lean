-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_fst_eq_basisDivisor_comap_theta
-- name    : WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_fst_eq_basisDivisor_comap_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/b84156cd-665d-5e8c-b7c9-e37ed7d9af1a
-- title:
--   Base change of the basis divisor along Proj of φ
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of relative group laws assigning, to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant, a relative group law on the structure morphism $\mathrm{Proj}(\mathtt{projModelGradingCR}\,W)\to\operatorname{Spec} T$; assume $\mathcal G$ is chord–tangent (for every such $T,W$ and every proof of $\mathrm{IsUnit}\,W.\Delta$ there is an evaluation map $ev$ with $\mathtt{IsPointsEval}$) and origin-identity (for every such $T,W$ there is a ring homomorphism $\chi$ from the origin chart ring to $T$ which is an origin-chart section of the unit section and kills $x/y$ and $z/y$). Let $T$ be an $A$-algebra, $K$ a field which is an $A$-algebra, $\iota : T\to K$ an $A$-algebra map, $W_0$ a Weierstrass curve over $T$ with $W_0.\Delta$ and $(W_0{\cdot}\mathrm{map}\,\iota).\Delta$ both units, and $n$ a natural number. Let $\varphi$ be a graded ring homomorphism from the graded ring of the projective model of $W_0$ to that of $W_0$ base changed along $\iota$, such that the irrelevant ideal downstairs is contained in the image under $\varphi$ of the irrelevant ideal upstairs, and such that $\varphi$ is a coefficient homomorphism: it sends the class of a constant $C\,a$ to the class of $C\,(\iota a)$ and the class of each coordinate $X_i$ to the class of $X_i$. Let $P_0,Q_0$ be sections of the projective model of $W_0$ over $\operatorname{Spec} T$ and $P',Q'$ sections of the projective model of the base-changed curve over $\operatorname{Spec} K$, compatible in the sense that $P'$ followed by $\mathrm{Proj.map}\,\varphi$ equals $\operatorname{Spec}\iota$ followed by $P_0$, and likewise for $Q',Q_0$. Finally let $\theta$ be a morphism from the pullback of the second projection of the relative self-product of the model of $W_0$ along $\operatorname{Spec}\iota$ to the relative self-product of the model of the base-changed curve, compatible with both projections: $\theta$ followed by the first projection and then $\mathrm{Proj.map}\,\varphi$ agrees with the two successive first projections, and $\theta$ followed by the second projection agrees with the second projection. Then the ideal sheaf datum $\mathtt{basisDivisor}(\mathcal G_{T,W_0},n,P_0,Q_0)$ — the product over the entries of the basis tuple of the kernel ideal sheaves of their graphs — pulled back along the first projection of the outer pullback equals $\mathtt{basisDivisor}(\mathcal G_{K,W_0\otimes K},n,P',Q')$ pulled back along $\theta$.
--
--   This is the base-change compatibility of the divisor $\sum_{a,b}[aP+bQ]$ attached to a pair of sections, for the passage from a Weierstrass curve over $T$ to its fibre over a field $K$ along an $A$-algebra map, with the comparison morphism supplied by a coefficient homomorphism of graded rings. It is one of the compatibility lemmas used in the extension statement for Drinfeld bases, [`WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map`](thm.html#WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_fst_eq_basisDivisor_comap_theta.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_fst_eq_basisDivisor_comap_theta
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (ι : T →ₐ[A] K)
    (W₀ : WeierstrassCurve T) (hΔ₀ : IsUnit W₀.Δ) (hΔ' : IsUnit (W₀.map ι.toRingHom).Δ) (n : ℕ)
    (φ : projModelGradingCR W₀ →+*ᵍ projModelGradingCR (W₀.map ι.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map ι.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₀)).map φ)
    (hφc : IsCoefficientHom W₀ ι.toRingHom φ)
    (P₀ Q₀ : Section W₀) (P' Q' : Section (W₀.map ι.toRingHom))
    (hP : P'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ P₀.1)
    (hQ : Q'.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Q₀.1)
    (θ : pullback (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))))
          (Spec.map (CommRingCat.ofHom ι.toRingHom)) ⟶
        pullback (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K))))
    (hθ₁ : θ ≫ pullback.fst _ _ ≫ Proj.map φ hφ =
      pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
        pullback.fst _ _)
    (hθ₂ : θ ≫ pullback.snd _ _ =
      pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) :
    (basisDivisor (𝒢 T W₀ hΔ₀) n P₀ Q₀).comap
        (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) =
      (basisDivisor (𝒢 K (W₀.map ι.toRingHom) hΔ') n P' Q').comap θ := by sorry
