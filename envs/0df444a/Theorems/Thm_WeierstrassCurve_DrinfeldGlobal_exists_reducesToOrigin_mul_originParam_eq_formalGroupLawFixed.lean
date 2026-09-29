-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/52d6f309-4c4d-5c22-ad75-e3fb41d26cbf
-- title:
--   Formal group law as parameter of the universal sum
-- statement:
--   Let $A$ be a Noetherian commutative domain, $W$ a Weierstrass curve over $A$ with invertible discriminant, and put $B = A[\![X_0,X_1]\!]$ (two-variable multivariate power series). Write $V$ for the projective Weierstrass model of $W$ base-changed along $A \to B$ and $\mathrm{Proj} \to \operatorname{Spec} B$ for its structure morphism. Let $G_0$ be a relative group law on this structure morphism over $B$ (multiplication, unit and inverse on $T$-points, natural in $T$, satisfying the group axioms). Assume: (i) there is a family of bijections, for every field $F$ over $B$, between the $F$-points of the model and the affine points of the base change of $V$ to $F$, carrying $G_0$-multiplication to addition of points and commuting with Galois twisting; (ii) the unit section $G_0.\mathrm{one}(\mathbf{1})$ factors as $\operatorname{Spec}$ of a ring homomorphism $\chi$ from the chart ring $\mathrm{Away}$ at the coordinate $Y$ into $B$, followed by the chart inclusion, with $\chi(x/y) = \chi(z/y) = 0$. Let $P_1, P_2$ be sections over $\operatorname{Spec} B$ and $\chi_1, \chi_2$ ring homomorphisms from the same chart ring to $B$ such that, for $I = (X_0, X_1)$, each $P_i$ is the composite of $\operatorname{Spec} \chi_i$ with the chart inclusion, with $-\chi_i(x/y) \in I$ and $\mathrm{originW}\,\chi_i \in I$, and moreover $-\chi_1(x/y) = X_0$, $-\chi_2(x/y) = X_1$. Then there is a ring homomorphism $\chi$ from the chart ring to $B$ that exhibits $G_0.\mathrm{mul}(\mathbf{1}, P_1, P_2)$ in the same way, with both $-\chi(x/y)$ and $\mathrm{originW}\,\chi$ in $I$, and with $-\chi(x/y)$ equal to $W.\mathrm{formalGroupLawFixed}$, the two-variable power series obtained by substituting $W.\mathrm{fgZ3Fixed}$ into $W.\mathrm{fgInv}$.
--
--   This identifies the group law on the projective Weierstrass model, evaluated at the two tautological sections with parameters $X_0$ and $X_1$, with the formal group law of $W$ in the parameter at the origin; it is the scheme-theoretic form of the addition formula for the Weierstrass formal group. It is used in the passage from a global group law to the formal group, feeding [`WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
    {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (W : WeierstrassCurve A) [W.IsElliptic]
    (G₀ : RelativeGroupLaw (MvPowerSeries (Fin 2) A)
      (projModelStrCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))))
    (hGpts : ∃ ev, IsPointsEval (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) G₀ ev)
    (hGone : ∃ χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A,
      IsOriginChartSection (G₀.one (𝟙 _)) χ ∧
        χ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = 0 ∧
        χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = 0)
    (P₁ P₂ : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A))))
    (χ₁ χ₂ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A)
    (h₁ : ReducesToOrigin P₁ χ₁ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}))
    (h₂ : ReducesToOrigin P₂ χ₂ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}))
    (hz₁ : originParam χ₁ = MvPowerSeries.X 0) (hz₂ : originParam χ₂ = MvPowerSeries.X 1) :
    ∃ χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A,
      ReducesToOrigin (G₀.mul (𝟙 _) P₁ P₂) χ
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}) ∧
      originParam χ = W.formalGroupLawFixed := by sorry
