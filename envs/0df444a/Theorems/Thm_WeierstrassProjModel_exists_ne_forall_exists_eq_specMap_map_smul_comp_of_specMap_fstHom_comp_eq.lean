-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
-- name    : WeierstrassProjModel.exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/8627ec2e-b72e-567e-bda5-5070c9ee93a1
-- title:
--   Dual-number lifts of a point form a line
-- statement:
--   Let $B$ be a commutative ring, $V$ a Weierstrass curve over $B$ whose discriminant $V.\Delta$ is a unit, $k$ a field and $f : B \to k$ a ring homomorphism. Write $E_V \to \operatorname{Spec} B$ for the structure morphism `projModelStrCR V`, namely $\operatorname{Proj}$ of the graded quotient of the polynomial ring in three variables by the homogeneous Weierstrass ideal of $V$, mapped to $\operatorname{Spec}$ of its degree-zero part and thence to $\operatorname{Spec} B$. Let $Q_0$ be a morphism $\operatorname{Spec} k \to E_V$ whose composite with the structure morphism is $\operatorname{Spec}(f)$. Writing $k[\varepsilon] =$ `DualNumber k`, the assertion is that there is a morphism $Q_1 : \operatorname{Spec} k[\varepsilon] \to E_V$ whose composite with the structure morphism is $\operatorname{Spec}$ of $B \to k \to k[\varepsilon]$, such that: (i) $\operatorname{Spec}$ of the projection $k[\varepsilon] \to k$, $\varepsilon \mapsto 0$, followed by $Q_1$ equals $Q_0$; (ii) $Q_1$ is not the constant lift, i.e. $\operatorname{Spec}$ of $k \to k[\varepsilon]$ followed by $Q_0$; and (iii) every such $Q$ over $B \to k[\varepsilon]$ reducing to $Q_0$ modulo $\varepsilon$ equals $\operatorname{Spec}$ of the endomorphism $a + b\varepsilon \mapsto a + cb\varepsilon$ of $k[\varepsilon]$, followed by $Q_1$, for some $c \in k$.
--
--   This expresses the one-dimensionality of the tangent space at a $k$-rational point of the fibre of a Weierstrass model with invertible discriminant: the $k[\varepsilon]$-points lifting $Q_0$ are exactly the scalar rescalings of one non-constant lift $Q_1$. It is used in the construction of homomorphisms into dual numbers for level-moduli packages, where such a tangent direction is needed at a point of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
    (B : Type) [CommRing B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ) (k : Type) [Field k] (f : B →+* k)
    (Q₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V)) :
    ∃ Q₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V),
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q₁.1 = Q₀.1 ∧
      Q₁.1 ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Q₀.1 ∧
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V),
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 = Q₀.1 →
        ∃ c : k, Q.1 = Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ Q₁.1 := by sorry
