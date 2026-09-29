-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/64299849-c778-59a3-a3a4-50474c3a265e
-- title:
--   Constant Verschiebung: reduction modulo ε, then constant extension
-- statement:
--   Let $A$ be a commutative ring and $\mathcal{G}$ a family of relative group laws assigning to each $A$-algebra $T$ and each projective Weierstrass curve over $T$ with unit discriminant a relative group law on its $\operatorname{Proj}$ model over $\operatorname{Spec} T$, assumed chord-tangent (for each such curve the sections over field points are identified, compatibly with addition and with Galois twisting, with the affine points of the base-changed curve) and origin-normalised (the identity section is cut out by a homomorphism from the origin chart ring killing both $x/y$ and $z/y$). Let $q$ be a prime, $k$ a field of characteristic $q$, and let the dual numbers $k[\varepsilon]$ be an $A$-algebra of characteristic $q$. Let $W, W^{(q)}$ be Weierstrass curves over $k[\varepsilon]$ with unit discriminants, let $W^{(q)}$ be constant, i.e. the base change of a curve $W^{(q)}_0$ over $k$, let $W_0$ over $k$ be the reduction of $W$ along $k[\varepsilon] \to k$, and assume the discriminant of $W_0 \otimes_k k[\varepsilon]$ is a unit. Let $V_q$ be a morphism from the $\operatorname{Proj}$ model of $W^{(q)}$ to that of $W$ over $\operatorname{Spec} k[\varepsilon]$ which is a homomorphism for $\mathcal{G}$ (for every scheme $S$ over $\operatorname{Spec} k[\varepsilon]$ and sections $x,y$ of the $W^{(q)}$ model over it, composing the $\mathcal{G}$-product with $V_q$ gives the $\mathcal{G}$-product of the composites), which is finite, flat, locally of finite presentation and surjective, of constant rank $m$ at every point, and which carries the zero section `kwZeroSect` of $W^{(q)}$ to that of $W$. Then there is a morphism $g$ from the $\operatorname{Proj}$ model of $W^{(q)}$ to that of $W_0 \otimes_k k[\varepsilon]$, over $\operatorname{Spec} k[\varepsilon]$, which is again a homomorphism for $\mathcal{G}$, finite, flat, locally of finite presentation, surjective, of rank $m$ at every point, and sends zero section to zero section, and which moreover satisfies: (i) every section $P$ of the $W^{(q)}$ model passing through an affine point whose coordinates are the images of some $x_0, y_0 \in k$ and with $P$ followed by $V_q$ equal to the zero section of $W$ also has $P$ followed by $g$ equal to the zero section of $W_0 \otimes_k k[\varepsilon]$; and (ii) for all graded ring homomorphisms $\varphi$, $\varphi'$ realising reduction modulo $\varepsilon$ on the graded coordinate rings of $W$ and of $W_0 \otimes_k k[\varepsilon]$ respectively (each sending the class of a constant $a$ to the class of its image and fixing the classes of the three coordinates, and each with the irrelevant ideal of its target contained in the image of the irrelevant ideal of its source), and given an identification of the reduction of $W_0 \otimes_k k[\varepsilon]$ with that of $W$, there are a scheme $Z$, a morphism $e$ from $Z$ to the $\operatorname{Proj}$ model of $W^{(q)}$ and an epimorphism $v$ from $Z$ onto the $\operatorname{Proj}$ model of the reduction of $W$ such that $e$ followed by $V_q$ equals $v$ followed by $\operatorname{Proj}.\mathrm{map}\,\varphi$, and $e$ followed by $g$ equals $v$ followed by the identification and then $\operatorname{Proj}.\mathrm{map}\,\varphi'$.
--
--   This is the construction of the constant form of the Verschiebung over the dual numbers: a given isogeny $V_q$ from a constant curve $W^{(q)}$ to $W$ over $k[\varepsilon]$ is replaced by the constant extension $g$ of its reduction modulo $\varepsilon$, with all formal properties (homomorphism for the group law, finiteness, flatness, local finite presentation, surjectivity, rank, behaviour at the origin) preserved, together with the two comparison properties: $g$ kills the constant sections killed by $V_q$, and $g$ agrees with $V_q$ after reduction modulo $\varepsilon$, tested through a common epimorphic source. It feeds the analysis of torsion lifting across the Frobenius twist, being used by [`WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber.lean

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] [Algebra A (DualNumber k)] [CharP (DualNumber k) q]
    (W Wq : WeierstrassCurve (DualNumber k)) (hΔW : IsUnit W.Δ) (hΔq : IsUnit Wq.Δ)
    (Wq₀ : WeierstrassCurve k) (hconst : Wq₀.map (algebraMap k (DualNumber k)) = Wq)
    (W₀ : WeierstrassCurve k) (hW₀ : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = W₀)
    (hΔ₀ : IsUnit (W₀.map (algebraMap k (DualNumber k))).Δ)
    (Vq : projModelCR Wq.toProjective ⟶ projModelCR W.toProjective)
    (hV : Vq ≫ projModelStrCR W.toProjective = projModelStrCR Wq.toProjective)
    (hVhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR Wq.toProjective)),
      (⟨((𝒢 (DualNumber k) Wq hΔq).mul t x y).1 ≫ Vq, by rw [Category.assoc, hV]; exact ((𝒢 (DualNumber k) Wq hΔq).mul t x y).2⟩ :
          SchemeHomOver t (projModelStrCR W.toProjective)) =
        (𝒢 (DualNumber k) W hΔW).mul t ⟨x.1 ≫ Vq, by rw [Category.assoc, hV]; exact x.2⟩ ⟨y.1 ≫ Vq, by rw [Category.assoc, hV]; exact y.2⟩)
    [IsFinite Vq] [Flat Vq] [LocallyOfFinitePresentation Vq] [Surjective Vq]
    (m : ℕ) (hVrk : ∀ p, Vq.finrank p = m)
    (hVO : (kwZeroSect (DualNumber k) Wq).1 ≫ Vq = (kwZeroSect (DualNumber k) W).1) :
    ∃ g : projModelCR Wq.toProjective ⟶ projModelCR (W₀.map (algebraMap k (DualNumber k))).toProjective,
      ∃ hg : g ≫ projModelStrCR (W₀.map (algebraMap k (DualNumber k))).toProjective = projModelStrCR Wq.toProjective,
      (∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR Wq.toProjective)),
        (⟨((𝒢 (DualNumber k) Wq hΔq).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 (DualNumber k) Wq hΔq).mul t x y).2⟩ :
            SchemeHomOver t (projModelStrCR (W₀.map (algebraMap k (DualNumber k))).toProjective)) =
          (𝒢 (DualNumber k) (W₀.map (algebraMap k (DualNumber k))) hΔ₀).mul t
            ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩) ∧
      IsFinite g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧
      (∀ p, g.finrank p = m) ∧
      (kwZeroSect (DualNumber k) Wq).1 ≫ g = (kwZeroSect (DualNumber k) (W₀.map (algebraMap k (DualNumber k)))).1 ∧
      (∀ (P : Section Wq.toProjective) (x₀ y₀ : k),
        IsSectionThrough P (algebraMap k (DualNumber k) x₀) (algebraMap k (DualNumber k) y₀) →
        P.1 ≫ Vq = (kwZeroSect (DualNumber k) W).1 →
        P.1 ≫ g = (kwZeroSect (DualNumber k) (W₀.map (algebraMap k (DualNumber k)))).1) ∧
      (∀ (φ : projModelGradingCR W.toProjective →+*ᵍ
            projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
        (_ : IsCoefficientHom W.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ)
        (φ' : projModelGradingCR (W₀.map (algebraMap k (DualNumber k))).toProjective →+*ᵍ
            projModelGradingCR (((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant
            (projModelGradingCR (((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map (algebraMap k (DualNumber k))).toProjective)).map φ')
        (_ : IsCoefficientHom (W₀.map (algebraMap k (DualNumber k))).toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ')
        (hW' : ((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom) =
          W.map (TrivSqZeroExt.fstHom k k k).toRingHom),
        ∃ (Z : Scheme) (e : Z ⟶ projModelCR Wq.toProjective)
          (v : Z ⟶ projModelCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective),
          Epi v ∧
          e ≫ Vq = v ≫ Proj.map φ hφ ∧
          e ≫ g = v ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫ Proj.map φ' hφ') := by sorry
