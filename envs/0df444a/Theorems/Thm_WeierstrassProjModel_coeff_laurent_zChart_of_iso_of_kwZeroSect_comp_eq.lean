-- Prove2me | Theorems.Thm_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
-- name    : WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/66881b52-a5af-5e72-b78c-a439e7ecf961
-- title:
--   Pole orders 2 and 3 with unit leading coefficients under a zero-preserving isomorphism
-- statement:
--   Let $T$ be a local commutative ring and let $W,W'$ be Weierstrass curves over $T$. Let $\Psi$ be an isomorphism of schemes between the $\mathrm{Proj}$ of the graded quotient of $T[X_0,X_1,X_2]$ by the homogeneous Weierstrass ideal of $W$ and the corresponding $\mathrm{Proj}$ for $W'$, assumed compatible with the structure morphisms to $\mathrm{Spec}\,T$ (so $\Psi.\mathrm{hom}$ followed by `projModelStrCR` of $W'$ is `projModelStrCR` of $W$) and carrying the zero section to the zero section (the underlying morphism of `kwZeroSect T W` followed by $\Psi.\mathrm{hom}$ equals that of `kwZeroSect T W'`). Let $e$ be a ring homomorphism from the $Z$-chart ring of $W'$, the degree-zero homogeneous localisation away from the class of $X_2$, to that of $W$, inducing $\Psi$ on these charts in the sense that $\mathrm{Spec}$ of $e$ followed by `zChartι` of $W'$ equals `zChartι` of $W$ followed by $\Psi.\mathrm{hom}$. Let $\Phi$ be a ring homomorphism from the $Y$-chart ring of $W$ (localisation away from the class of $X_1$) to $T[[Z]]$ sending each degree-zero constant $t$ to the constant series $t$, with $\Phi(X/Y)=-Z$ and $\Phi(Z/Y)=-W.\mathrm{formalW}$, the series whose $n$-th coefficient is the $n$-th coefficient of $W$'s $n$-th Weierstrass iterate. Let $\mathrm{lam}$ be a ring homomorphism from the $Z$-chart ring of $W$ to the Laurent series $T((Z))$ sending degree-zero constants to constants and satisfying $\mathrm{lam}(X/Z)\cdot\Phi(Z/Y)=\Phi(X/Y)$ and $\mathrm{lam}(Y/Z)\cdot\Phi(Z/Y)=1$, both read inside $T((Z))$ via the inclusion of power series. Then the Laurent coefficients of $\mathrm{lam}(e(X'/Z'))$ vanish in all degrees $n<-2$ and its coefficient in degree $-2$ is a unit of $T$, while the coefficients of $\mathrm{lam}(e(Y'/Z'))$ vanish in all degrees $n<-3$ and its coefficient in degree $-3$ is a unit.
--
--   This is the local computation showing that an isomorphism of projective Weierstrass models respecting the base and the zero section transports the affine coordinates to functions with poles of order exactly $2$ and $3$ at the origin, with invertible leading Laurent coefficients — the analytic input to the classical fact that such an isomorphism is given by a Weierstrass variable change. It is used by [`WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing`](thm.html#WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing), which extracts the variable change over an Artinian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_FormalGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
    (T : Type) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) := by sorry
