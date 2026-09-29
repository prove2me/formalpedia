-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/7d158766-efd9-5408-ac24-29d209624856
-- title:
--   Flat degree-q subscheme of ker V_q killed by g
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family assigning, to every $A$-algebra $T$ and every projective Weierstrass model $W$ over $T$ with invertible discriminant, a relative group law on the structure morphism $\mathrm{projModelStrCR}\,W \to \operatorname{Spec} T$; assume $\mathcal G$ is chord–tangent (each such group law is matched, by an additive and Galois-equivariant bijection, with the affine Mordell–Weil group over every field extension) and origin-identity (the identity section of each such group law is cut out by a ring homomorphism from the chart where the second coordinate is inverted which kills $x/y$ and $z/y$). Let $q$ be a prime, $B$ an $A$-algebra, $V$ a Weierstrass curve over $B$ with $\Delta_V$ a unit, $k$ a field of characteristic $q$, and $\beta : B \to k[\varepsilon]$ a ring homomorphism into the dual numbers, with $k[\varepsilon]$ an $A$-algebra of characteristic $q$. Let $Q$ be a morphism $\operatorname{Spec} k[\varepsilon] \to \mathrm{projModelCR}\,V$ over $\operatorname{Spec}\beta$ which is $q$-torsion for $\mathcal G\,B\,V$ and whose composite with $\operatorname{Spec}$ of the projection $k[\varepsilon]\to k$ differs from the corresponding identity section. Write $W = V\otimes_\beta k[\varepsilon]$ and $W^{(q)}$ for its twist by the $q$-power Frobenius of $k[\varepsilon]$, both assumed to have unit discriminant. Assume given: a morphism $\Phi : \mathrm{projModelCR}\,W \to \mathrm{projModelCR}\,W^{(q)}$ over $\operatorname{Spec} k[\varepsilon]$ which on the chart where the third coordinate is inverted comes from a ring homomorphism sending $x$ and $y$ of $W^{(q)}$ to the $q$-th powers of $x$ and $y$ of $W$, and which is a homomorphism for the group laws $\mathcal G\,k[\varepsilon]\,W$ and $\mathcal G\,k[\varepsilon]\,W^{(q)}$ on all scheme-valued points; a morphism $V_q : \mathrm{projModelCR}\,W^{(q)} \to \mathrm{projModelCR}\,W$ over $\operatorname{Spec} k[\varepsilon]$ with $\Phi$ followed by $V_q$ equal to the multiplication-by-$q$ endomorphism of the group law on $W$; and a Weierstrass curve $W_3$ over $k[\varepsilon]$ with unit discriminant together with a morphism $g : \mathrm{projModelCR}\,W^{(q)} \to \mathrm{projModelCR}\,W_3$ over $\operatorname{Spec} k[\varepsilon]$ which is a homomorphism for the group laws, and such that every section $P$ of $\mathrm{projModelCR}\,W^{(q)}$ over $\operatorname{Spec} k[\varepsilon]$ passing through affine coordinates lying in the image of $k$ and satisfying $P$ followed by $V_q$ equals the standard zero section of $W$, also satisfies that $P$ followed by $g$ is the standard zero section of $W_3$. Then there exist a scheme $K$ and a closed immersion $\iota : K \to \mathrm{projModelCR}\,W^{(q)}$ whose composite with the structure morphism to $\operatorname{Spec} k[\varepsilon]$ is flat, locally of finite presentation and of rank $q$ at every point, and such that $\iota$ followed by $V_q$, respectively by $g$, factors through the structure morphism followed by the identity section of the group law on $W$, respectively on $W_3$.
--
--   The statement produces, inside the Frobenius twist $E_{W^{(q)}}$ over the dual numbers $k[\varepsilon]$, a finite flat closed subscheme of degree $q$ which lies in the kernel of the Verschiebung-type factor $V_q$ of multiplication by $q$ and is annihilated by the auxiliary homomorphism $g$; the input $Q$ is a $q$-torsion point over $k[\varepsilon]$ not reducing to the origin. It is used in the deduction that $E_{W^{(q)}}$ is isomorphic to a Frobenius base change, in the analysis of $q$-torsion of Weierstrass models over $k[\varepsilon]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one.lean

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra
  WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one
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
    (Φ : projModelCR (V.map β).toProjective ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective = projModelStrCR (V.map β).toProjective)
    (hZ : ∃ ψ : ZChartRing ((V.map β).map (frobenius (DualNumber k) q)).toProjective →+* ZChartRing (V.map β).toProjective,
        ψ (xOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = xOverZ (V.map β).toProjective ^ q ∧
        ψ (yOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = yOverZ (V.map β).toProjective ^ q ∧
        zChartι (V.map β).toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR (V.map β).toProjective)),
      (⟨((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)) =
        (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩)

    (Vq : projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective ⟶ projModelCR (V.map β).toProjective)
    (hV : Vq ≫ projModelStrCR (V.map β).toProjective = projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hVq : Φ ≫ Vq = (𝒢 (DualNumber k) (V.map β) hΔW).schemeNsmul q)

    (W₃ : WeierstrassCurve (DualNumber k)) (hΔ₃ : IsUnit W₃.Δ)
    (g : projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective ⟶ projModelCR W₃.toProjective)
    (hg : g ≫ projModelStrCR W₃.toProjective = projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hghom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)),
      (⟨((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) =
        (𝒢 (DualNumber k) W₃ hΔ₃).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩)
    (hK : ∀ (P : Section ((V.map β).map (frobenius (DualNumber k) q)).toProjective) (x₀ y₀ : k),
      IsSectionThrough P (algebraMap k (DualNumber k) x₀) (algebraMap k (DualNumber k) y₀) →
      P.1 ≫ Vq = (kwZeroSect (DualNumber k) (V.map β)).1 →
      P.1 ≫ g = (kwZeroSect (DualNumber k) W₃).1) :
    ∃ (K : Scheme) (ι : K ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective),
      IsClosedImmersion ι ∧
      Flat (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ∧
      LocallyOfFinitePresentation (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ∧
      (∀ s, (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective).finrank s = q) ∧
      ι ≫ Vq = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫
        ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 ∧
      ι ≫ g = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫
        ((𝒢 (DualNumber k) W₃ hΔ₃).one (𝟙 _)).1 := by sorry
