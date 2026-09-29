-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/835b82a8-f1af-5287-a141-4c0dc97eee58
-- title:
--   Frobenius on charts gives a homomorphism of group laws
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$: an assignment, to every commutative $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant, of a relative group law on the structure morphism `projModelStrCR` of the $\mathrm{Proj}$ model of $W$ over $\operatorname{Spec} T$. Assume $\mathcal G$ is chord–tangent, i.e. for each such $T$, $W$, $h\Delta$ there is a bijection $ev$ between field-valued points of the model and points of the affine curve after base change which turns the law's multiplication into addition and is equivariant for Galois twisting, and that $\mathcal G$ has the origin as identity, i.e. there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ through which the law's unit section factors along `originChartι`, with $\chi(\mathrm{xOverY}) = \chi(\mathrm{zOverY}) = 0$. Let $q$ be a prime, $T$ a commutative $A$-algebra of characteristic $q$, and $W$ a Weierstrass curve over $T$ such that both $\Delta(W)$ and $\Delta(W^{(q)})$ are units, where $W^{(q)} = W.\mathrm{map}(\mathrm{frobenius}\ T\ q)$. Let $\Phi$ be a morphism from the $\mathrm{Proj}$ model of $W$ to that of $W^{(q)}$ with $\Phi$ followed by the structure morphism of the target equal to the structure morphism of the source. Assume further: there is a ring homomorphism $\psi$ from the $z$-chart ring of $W^{(q)}$ to that of $W$ sending $\mathrm{xOverZ}$ and $\mathrm{yOverZ}$ to the $q$-th powers of $\mathrm{xOverZ}$ and $\mathrm{yOverZ}$, with `zChartι` of $W$ followed by $\Phi$ equal to $\operatorname{Spec}(\psi)$ followed by `zChartι` of $W^{(q)}$; and likewise a ring homomorphism from the origin chart ring of $W^{(q)}$ to that of $W$ sending $\mathrm{xOverY}$ and $\mathrm{zOverY}$ to their $q$-th powers and compatible with $\Phi$ over `originChartι`. Then for every scheme $S$, every $t : S \to \operatorname{Spec} T$ and all points $x, y$ of the model of $W$ over $t$, composing the product $(\mathcal G\,T\,W\,h\Delta).\mathrm{mul}\ t\ x\ y$ with $\Phi$ gives the same point of the model of $W^{(q)}$ over $t$ as the product $(\mathcal G\,T\,W^{(q)}\,h\Delta_q).\mathrm{mul}\ t$ of $x$ followed by $\Phi$ and $y$ followed by $\Phi$.
--
--   This is the statement that the relative Frobenius $E_W \to E_{W^{(q)}}$ in characteristic $q$ — here characterised by acting as the $q$-th power map on the two standard charts of the $\mathrm{Proj}$ model — is a homomorphism for the pinned family of group laws, on points valued in an arbitrary test scheme over $\operatorname{Spec} T$. It is used in the analysis of $q$-power torsion and of Frobenius-twisted level structures, in particular in the construction of variable changes matching $W^{(q)}$ with the image of $W$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔq : IsUnit (W.map (frobenius T q)).Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    (⟨((𝒢 T W hΔ).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 T W hΔ).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩ := by sorry
