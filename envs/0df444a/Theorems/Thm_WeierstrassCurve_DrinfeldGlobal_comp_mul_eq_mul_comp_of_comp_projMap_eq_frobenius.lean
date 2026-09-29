-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_comp_projMap_eq_frobenius
-- name    : WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_comp_projMap_eq_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/8b78606e-54ec-5fde-86a1-11a873ace606
-- title:
--   Frobenius descent: Φ is a homomorphism of the group laws
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of relative group laws assigning, to every $A$-algebra $T$ and every projective Weierstrass curve $V$ over $T$ with $\Delta(V)$ a unit, a relative group law on the structure morphism $\mathrm{projModelStrCR}\,V : \mathrm{Proj}$ of the graded quotient ring of $V$ to $\operatorname{Spec} T$. Assume $\mathcal G$ is chord–tangent (for each such $T,V,h_\Delta$ there is an $\mathrm{ev}$ with `IsPointsEval`) and origin-pinned: for each such $T,V,h_\Delta$ there is a ring homomorphism $\chi$ from the origin chart ring of $V$ to $T$ which is an origin-chart section of the unit $\mathcal G_T(V)(\mathbb 1)$ and kills $x/y$ and $z/y$. Let $q$ be a prime, $T$ an $A$-algebra of characteristic $q$, and $W$ a Weierstrass curve over $T$ with $\Delta(W)$ and $\Delta(W^{(q)})$ units, where $W^{(q)}$ is the base change of $W$ along the Frobenius endomorphism $a \mapsto a^q$ of $T$. Let $\Phi$ be a morphism from the projective model of $W$ to that of $W^{(q)}$ with $\Phi$ followed by the structure morphism of $W^{(q)}$ equal to that of $W$, and let $\varphi$ be a graded ring homomorphism between the two graded quotient rings whose induced $\mathrm{Proj}$-map is defined ($h\varphi$: the irrelevant ideal downstairs lies in the image of the irrelevant ideal upstairs) and which is a coefficient homomorphism over Frobenius, i.e. $\varphi$ sends the class of a constant $C\,a$ to the class of $C\,(a^q)$ and fixes the classes of the three coordinates. Assume $q = 0$ in $\Gamma(\mathrm{Proj}, \top)$ for the model of $W$ and that $\Phi$ followed by $\mathrm{Proj}(\varphi)$ is the absolute $q$-Frobenius (exponent $1$) of that model. Then for every scheme $S$, every $t : S \to \operatorname{Spec} T$ and all $x, y$ in the set of morphisms $S \to$ model of $W$ composing with the structure morphism to give $t$, the composite of $\mathcal G_T(W)$-multiplication $x \cdot y$ with $\Phi$ equals the $\mathcal G_T(W^{(q)})$-product of $x$ followed by $\Phi$ and $y$ followed by $\Phi$, as elements over $t$.
--
--   This is the core step showing that a morphism over $T$ from the model of $W$ to the model of its Frobenius twist, which lifts the absolute $q$-Frobenius through the coefficient projection, respects the group laws of the family; it is the relative-scheme form of the statement that Frobenius is an isogeny. It is used by [`WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow), where the hypothesis on $\Phi$ is verified chart by chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_comp_projMap_eq_frobenius.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra
  WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_comp_projMap_eq_frobenius
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔq : IsUnit (W.map (frobenius T q)).Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map (frobenius T q)).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (frobenius T q)).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective (frobenius T q) φ)
    (hE : (q : Γ(projModelCR W.toProjective, ⊤)) = 0)
    (hΨ : Φ ≫ Proj.map φ hφ = (projModelCR W.toProjective).frobenius q 1 Fact.out hE)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    (⟨((𝒢 T W hΔ).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 T W hΔ).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩ := by sorry
