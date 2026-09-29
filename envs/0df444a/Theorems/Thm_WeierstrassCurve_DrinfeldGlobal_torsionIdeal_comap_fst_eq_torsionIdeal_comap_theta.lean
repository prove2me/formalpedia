-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
-- name    : WeierstrassCurve.DrinfeldGlobal.torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/949062e3-79f8-5e7b-9cc1-3375135bca6c
-- title:
--   Base change of the n-torsion ideal sheaf along θ
-- statement:
--   Fix a commutative ring $A$ and a family $\mathcal G$ of relative group laws: for every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant, $\mathcal G$ supplies a relative group law on the structure morphism `projModelStrCR W`. Two hypotheses on $\mathcal G$ are assumed: `IsChordTangent`, i.e. for all such $T$, $W$, $\mathrm{hΔ}$ there is an evaluation datum `ev` with `IsPointsEval W (𝒢 T W hΔ) ev`; and `IsOriginIdentity`, i.e. for all such data there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ which is an origin-chart section of the identity element of $\mathcal G$ and kills both $x/y$ and $z/y$. Let $T$ be an $A$-algebra, $K$ a field that is an $A$-algebra, $\iota : T \to K$ an $A$-algebra homomorphism, $W_0$ a Weierstrass curve over $T$ with $\Delta(W_0)$ a unit and $\Delta(W_0\otimes_\iota K)$ a unit, and $n$ a natural number. Let $\varphi$ be a graded ring homomorphism from the graded quotient ring `projModelGradingCR W₀` to that of $W_0 \otimes_\iota K$, such that the irrelevant ideal of the target is contained in the image under $\varphi$ of the irrelevant ideal of the source (so that `Proj.map φ hφ` exists), and such that $\varphi$ is a coefficient homomorphism: it carries the class of a constant $C\,a$ to the class of $C\,(\iota a)$ and fixes the classes of the three coordinates $X_i$. Let $\theta$ be a morphism from the pullback of `pullback.snd (projModelStrCR W₀) (𝟙 (Spec T))` along $\mathrm{Spec}(\iota)$ to the pullback of `projModelStrCR (W₀.map ι)` along $\mathbf 1_{\mathrm{Spec}\,K}$, subject to two compatibilities: $\theta$ followed by the first projection and then by `Proj.map φ hφ` agrees with the first projection followed by the first projection, and $\theta$ followed by the second projection agrees with the second projection. The conclusion is an equality of ideal sheaf data on the common source: the $n$-torsion ideal of $\mathcal G\,T\,W_0$ — that is, the kernel ideal sheaf of the first projection of the pullback of the $n$-fold multiplication morphism against the identity section, composed with the canonical map to the pullback along the identity — pulled back along the first projection, coincides with the $n$-torsion ideal of $\mathcal G\,K\,(W_0\otimes_\iota K)$ pulled back along $\theta$.
--
--   This is the base-change compatibility of the scheme-theoretic $n$-torsion subscheme: multiplication by $n$ and the identity section are cartesian over the change of base $T \to K$, so the $n$-torsion ideal sheaf of the base-changed projective Weierstrass model is the pullback along $\theta$ of the $n$-torsion ideal sheaf upstairs. It is one of the geometric inputs to [`WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map`](thm.html#WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map), the extension of Drinfeld level structures from the fibre over $K$ to the model over $T$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (ι : T →ₐ[A] K)
    (W₀ : WeierstrassCurve T) (hΔ₀ : IsUnit W₀.Δ) (hΔ' : IsUnit (W₀.map ι.toRingHom).Δ) (n : ℕ)
    (φ : projModelGradingCR W₀ →+*ᵍ projModelGradingCR (W₀.map ι.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map ι.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₀)).map φ)
    (hφc : IsCoefficientHom W₀ ι.toRingHom φ)
    (θ : pullback (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))))
          (Spec.map (CommRingCat.ofHom ι.toRingHom)) ⟶
        pullback (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K))))
    (hθ₁ : θ ≫ pullback.fst _ _ ≫ Proj.map φ hφ =
      pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
        pullback.fst _ _)
    (hθ₂ : θ ≫ pullback.snd _ _ =
      pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) :
    (torsionIdeal (𝒢 T W₀ hΔ₀) n).comap
        (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) =
      (torsionIdeal (𝒢 K (W₀.map ι.toRingHom) hΔ') n).comap θ := by sorry
