-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isUnit_map_residue_nthSeries_eq_mul_X_pow_of_isDrinfeldBasisAdic_zero
-- name    : WeierstrassCurve.exists_isUnit_map_residue_nthSeries_eq_mul_X_pow_of_isDrinfeldBasisAdic_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/e4c62ab2-fa84-5c82-b6cc-4e09b230efbd
-- title:
--   Residue of [q]_F is a unit times X^{q^2}
-- statement:
--   Let $T$ be a commutative local ring, $W$ a Weierstrass curve over $T$ that is elliptic, and $F$ a formal group over $T$ whose underlying two-variable power series is $W$'s fixed formal group law `W.formalGroupLawFixed`; let $q$ be a prime natural number. Here `F.nthSeries` is defined recursively by `nthSeries 0 = 0` and `nthSeries (n+1)` = the substitution of `(F.nthSeries n, X)` into the group law of $F$, so that `F.nthSeries q` is the multiplication-by-$q$ series $[q]_F$. The hypothesis is that the formal group of the reduced curve $W \otimes_T k$, for $k$ the residue field of $T$ and the reduction taken along `residue T`, satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`: with respect to the zero ideal of $k$, there is a unit power series $u$ over $k$ with $[q]$-series equal to $u$ times the power series `drinfeldDivisor q 0 0` attached to the pair of points $(0,0)$. The conclusion is that there exists a unit $v \in k\llbracket X \rrbracket$ with $$\mathrm{map}(\mathrm{residue}\,T)\bigl(F.\mathrm{nthSeries}\ q\bigr) = v \cdot X^{q \cdot q}.$$
--
--   This records, in the language of formal groups, that a Drinfeld $q$-basis at the origin $(0,0)$ on the closed fibre forces the reduction of $[q]_F$ to have a zero of order exactly $q^2$, the shape characteristic of supersingular reduction. It is used in the passage from a global Drinfeld $\Gamma(q)$-basis with supersingular reduction to the corresponding statement for the formal group of the curve, being cited by [`WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero`](thm.html#WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isUnit_map_residue_nthSeries_eq_mul_X_pow_of_isDrinfeldBasisAdic_zero.lean

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

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.exists_isUnit_map_residue_nthSeries_eq_mul_X_pow_of_isDrinfeldBasisAdic_zero
    {T : Type u} [CommRing T] [IsLocalRing T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (q : ℕ) [Fact q.Prime]
    (hss : (W.map (residue T)).formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0) :
    ∃ v : PowerSeries (ResidueField T), IsUnit v ∧
      PowerSeries.map (residue T) (F.nthSeries q) = v * PowerSeries.X ^ (q * q) := by sorry
