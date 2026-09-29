-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6ed7ce70-96f5-5148-9c1c-aa47b7ed5708
-- title:
--   Base change comparison of relative group laws on projective Weierstrass models
-- statement:
--   Let $B$ and $T$ be commutative rings, let $V$ be a Weierstrass curve over $B$ which is elliptic, and let $f : B \to T$ be a ring homomorphism, so that $V.map f$ is the Weierstrass curve over $T$ obtained by applying $f$ to the coefficients. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj}$ of the graded ring of the projective model of $V$ over $\operatorname{Spec} B$, and $L$ one on the corresponding structure morphism for $V.map f$ over $\operatorname{Spec} T$; assume the underlying morphism of the unit section $G.\mathrm{one}$ at the identity of $\operatorname{Spec} B$ is the zero section `kwZeroSect B V`, and likewise that the unit of $L$ at the identity of $\operatorname{Spec} T$ is `kwZeroSect T (V.map f)`. The assertion is that there exist a morphism $\Phi$ from the projective model of $V.map f$ to that of $V$ and a proof `hsq` that $\Phi$ followed by the structure morphism of the model of $V$ equals the structure morphism of the model of $V.map f$ followed by $\operatorname{Spec}$ of $f$, such that: (i) that commutative square, with $\Phi$ and $\operatorname{Spec} f$ as the horizontal sides, is cartesian; (ii) for every $n \in \mathbb{N}$ and every section $S$ of the model of $V.map f$ over the identity of $\operatorname{Spec} T$, composing the $n$-th iterate $L.\mathrm{nsmul}$ of $S$ (defined by $0 \mapsto$ unit, $n+1 \mapsto$ the $L$-product of the $n$-th iterate with $S$) with $\Phi$ gives the $n$-th iterate $G.\mathrm{nsmul}$, over $\operatorname{Spec} f$, of the section $S$ followed by $\Phi$; (iii) the unit of $L$ followed by $\Phi$ is the unit of $G$ over $\operatorname{Spec} f$; and (iv) for every section $S$ and all $x, y \in T$, the predicate `IsSectionThrough S x y` — that $S$ factors as $\operatorname{Spec}$ of a ring homomorphism from the $Z$-chart ring of the model of $V.map f$ to $T$ followed by the chart inclusion `zChartι`, with the two affine coordinates sent to $x$ and $y$ — holds if and only if there is a ring homomorphism $\chi$ from `ZChartRing V.toProjective` to $T$ with $S$ followed by $\Phi$ equal to $\operatorname{Spec}$ of $\chi$ followed by `zChartι` for $V$, and $\chi(\mathtt{xOverZ}) = x$, $\chi(\mathtt{yOverZ}) = y$.
--
--   This packages the base change of the projective Weierstrass model along $\operatorname{Spec} f$ into a single cartesian comparison morphism that is compatible with the two relative group laws (unit, iterated addition) and translates the affine $Z$-chart description of sections from the base-changed curve to the original one. It is the transfer device used downstream in the criteria for a section to be $n$-torsion in terms of division polynomials and in the construction of the closed immersion attached to torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
    {B T : Type} [CommRing B] [CommRing T] (V : WeierstrassCurve B) [V.IsElliptic] (f : B →+* T)
    (G : RelativeGroupLaw B (projModelStrCR V.toProjective)) (hG : (G.one (𝟙 _)).1 = (kwZeroSect B V).1)
    (L : RelativeGroupLaw T (projModelStrCR (V.map f).toProjective))
    (hL : (L.one (𝟙 _)).1 = (kwZeroSect T (V.map f)).1) :
    ∃ (Φ : projModelCR (V.map f).toProjective ⟶ projModelCR V.toProjective)
      (hsq : Φ ≫ projModelStrCR V.toProjective = projModelStrCR (V.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f)),
      IsPullback Φ (projModelStrCR (V.map f).toProjective) (projModelStrCR V.toProjective)
        (Spec.map (CommRingCat.ofHom f)) ∧
      (∀ (n : ℕ) (S : Section (V.map f).toProjective),
        (L.nsmul (𝟙 _) n S).1 ≫ Φ =
          (G.nsmul (Spec.map (CommRingCat.ofHom f)) n
            ⟨S.1 ≫ Φ, by rw [Category.assoc, hsq, ← Category.assoc, S.2, Category.id_comp]⟩).1) ∧
      ((L.one (𝟙 _)).1 ≫ Φ = (G.one (Spec.map (CommRingCat.ofHom f))).1) ∧
      (∀ (S : Section (V.map f).toProjective) (x y : T),
        IsSectionThrough S x y ↔
          ∃ χ : ZChartRing V.toProjective →+* T, S.1 ≫ Φ = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V.toProjective ∧
            χ (xOverZ V.toProjective) = x ∧ χ (yOverZ V.toProjective) = y) := by sorry
