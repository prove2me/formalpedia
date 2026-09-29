-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/152a2c14-2bb2-5ea0-b197-d9b60512caff
-- title:
--   Trivialising a deformation from a q-torsion point and Frobenius
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of relative group laws, assigning to every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every witness that $\Delta_W$ is a unit a relative group law on the structure morphism `projModelStrCR W`; assume $\mathcal G$ is chord–tangent (for each such datum there is a bijection between the points of the projective model over a field extension and the points of the associated affine curve which is additive and compatible with Galois twisting) and origin-identity (for each datum the identity section is cut out by a ring homomorphism from the origin chart ring sending $x/y$ and $z/y$ to $0$). Let $q$ be a prime, $B$ an $A$-algebra, $V$ a Weierstrass curve over $B$ with $\Delta_V$ a unit, $k$ a field of characteristic $q$ and $\beta : B \to k[\varepsilon]$ a ring homomorphism into the dual numbers, the latter being an $A$-algebra of characteristic $q$. Let $Q$ be a section of `projModelStrCR V.toProjective` over $\operatorname{Spec}\beta$ such that the $q$-fold iterate of the group law applied to $Q$ is the identity section, while the composite of $\operatorname{Spec}$ of the projection $k[\varepsilon] \to k$ with $Q$ differs from the identity section over $\operatorname{Spec}$ of the reduced homomorphism; thus $Q$ is a $q$-torsion point that is nonzero modulo $\varepsilon$. Write $W = V\otimes_\beta k[\varepsilon]$, its Frobenius twist $W^{(q)} = W$ base changed along `frobenius (DualNumber k) q`, and $W' = (V\otimes_{\beta_0} k)\otimes_k k[\varepsilon]$ with $\beta_0$ the reduction of $\beta$; assume $\Delta_W$ and $\Delta_{W^{(q)}}$ are units and that $W'$ and $W$ have the same reduction modulo $\varepsilon$. Let $\Phi : \mathrm{projModelCR}\,W \to \mathrm{projModelCR}\,W^{(q)}$ be a morphism over $\operatorname{Spec} k[\varepsilon]$ which on the $Z$-chart and on the origin chart is induced by ring homomorphisms raising $x/z, y/z$, respectively $x/y, z/y$, to the $q$-th power compatibly with the chart immersions, which is finite, flat, locally of finite presentation and surjective, carries the zero section `kwZeroSect` of $W$ to that of $W^{(q)}$, is a homomorphism for the two group laws on the points of every test scheme over $\operatorname{Spec} k[\varepsilon]$, and whose kernel on every test scheme is killed by the multiplication-by-$q$ morphism `schemeNsmul q` of the group law on $W$. Then there is an isomorphism $\Psi$ from $\mathrm{projModelCR}\,W$ to $\mathrm{projModelCR}\,W'$ whose forward direction lies over $\operatorname{Spec} k[\varepsilon]$ and carries the zero section of $W$ to that of $W'$, together with graded ring homomorphisms $\varphi$ from the grading of $W$ to that of $W$ modulo $\varepsilon$ and $\varphi'$ from the grading of $W'$ to that of $W'$ modulo $\varepsilon$, each satisfying the inclusion of irrelevant ideals required for `Proj.map` and each a coefficient homomorphism for the projection $k[\varepsilon]\to k$ (the class of a constant $C\,a$ goes to $C$ of its reduction, and the class of $X_i$ to $X_i$), such that `Proj.map φ hφ` followed by $\Psi$ equals the identification of the two reductions coming from the equality of $W'$ and $W$ modulo $\varepsilon$ followed by `Proj.map φ' hφ'`; that is, $\Psi$ is the identity on the fibre modulo $\varepsilon$.
--
--   This is the rigidity step which converts a nonzero $q$-torsion point over the dual numbers, together with a relative Frobenius factorisation of multiplication by $q$, into an isomorphism of the deformation $W$ with the constant curve $W' = W_0\otimes_k k[\varepsilon]$ inducing the identity modulo $\varepsilon$. It is used to produce the corresponding variable change, in [`WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_map_eq_map_map_of_nsmul_eq_one_of_nthSeries_eq_mul_X_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_map_eq_map_map_of_nsmul_eq_one_of_nthSeries_eq_mul_X_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    (k : Type) [Field k] [CharP k q] (β : B →+* DualNumber k)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom β)) (projModelStrCR V))
    (hQq : (𝒢 B V hΔ).nsmul _ q Q = (𝒢 B V hΔ).one _)
    (hQ0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 ≠
      ((𝒢 B V hΔ).one (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)))).1)
    [Algebra A (DualNumber k)] [CharP (DualNumber k) q]
    (hΔW : IsUnit (V.map β).Δ) (hΔq : IsUnit ((V.map β).map (frobenius (DualNumber k) q)).Δ)
    (hW' : (((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map (algebraMap k (DualNumber k)))).map
        (TrivSqZeroExt.fstHom k k k).toRingHom = (V.map β).map (TrivSqZeroExt.fstHom k k k).toRingHom)
    (Φ : projModelCR (V.map β).toProjective ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective = projModelStrCR (V.map β).toProjective)
    (hZ : ∃ ψ : ZChartRing ((V.map β).map (frobenius (DualNumber k) q)).toProjective →+* ZChartRing (V.map β).toProjective,
        ψ (xOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = xOverZ (V.map β).toProjective ^ q ∧
        ψ (yOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = yOverZ (V.map β).toProjective ^ q ∧
        zChartι (V.map β).toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hY : ∃ ψ : OriginChartRing ((V.map β).map (frobenius (DualNumber k) q)).toProjective →+* OriginChartRing (V.map β).toProjective,
        ψ (xOverY ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = xOverY (V.map β).toProjective ^ q ∧
        ψ (zOverY ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = zOverY (V.map β).toProjective ^ q ∧
        originChartι (V.map β).toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    [IsFinite Φ] [Flat Φ] [LocallyOfFinitePresentation Φ] [Surjective Φ]
    (hΦO : (kwZeroSect (DualNumber k) (V.map β)).1 ≫ Φ = (kwZeroSect (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q))).1)
    (hΦhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR (V.map β).toProjective)),
      (⟨((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)) =
        (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩)
    (hker : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x : SchemeHomOver t (projModelStrCR (V.map β).toProjective)),
      (⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)) = (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).one t →
      (⟨x.1 ≫ (𝒢 (DualNumber k) (V.map β) hΔW).schemeNsmul q, by rw [Category.assoc, (𝒢 (DualNumber k) (V.map β) hΔW).schemeNsmul_over]; exact x.2⟩ :
        SchemeHomOver t (projModelStrCR (V.map β).toProjective)) = (𝒢 (DualNumber k) (V.map β) hΔW).one t) :
    ∃ (Ψ : projModelCR (V.map β).toProjective ≅
        projModelCR ((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map (algebraMap k (DualNumber k))).toProjective),
      Ψ.hom ≫ projModelStrCR ((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
          (algebraMap k (DualNumber k))).toProjective = projModelStrCR (V.map β).toProjective ∧
      (kwZeroSect (DualNumber k) (V.map β)).1 ≫ Ψ.hom =
        (kwZeroSect (DualNumber k) ((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
          (algebraMap k (DualNumber k)))).1 ∧
      ∃ (φ : projModelGradingCR (V.map β).toProjective →+*ᵍ
          projModelGradingCR ((V.map β).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR ((V.map β).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR (V.map β).toProjective)).map φ)
        (φ' : projModelGradingCR ((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
            (algebraMap k (DualNumber k))).toProjective →+*ᵍ
          projModelGradingCR ((((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
            (algebraMap k (DualNumber k)))).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR ((((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
            (algebraMap k (DualNumber k)))).map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR ((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
            (algebraMap k (DualNumber k))).toProjective)).map φ'),
        IsCoefficientHom (V.map β).toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ ∧
        IsCoefficientHom ((V.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)).map
          (algebraMap k (DualNumber k))).toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ' ∧
        Proj.map φ hφ ≫ Ψ.hom =
          eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫ Proj.map φ' hφ' := by sorry
