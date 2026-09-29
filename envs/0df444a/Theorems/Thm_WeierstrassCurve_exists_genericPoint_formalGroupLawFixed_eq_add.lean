-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_genericPoint_formalGroupLawFixed_eq_add
-- name    : WeierstrassCurve.exists_genericPoint_formalGroupLawFixed_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/6f85058b-8a3c-51c5-bc2c-63620cf004d3
-- title:
--   Generic point of the formal group law is the sum of coordinate generic points
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and let $W$ be a Weierstrass curve over $R$ whose discriminant is a unit (`IsElliptic`). Write $\iota$ for the canonical map `genι` of $R[[X_0,X_1]]$ into the field `GenK (Fin 2) R`, and for a two-variable series $t$ put $w(t) =$ `fgGenW` $t$, the substitution of $t$ into the one-variable series `formalW`; when $\iota(w(t)) \ne 0$ and $t$ is substitutable, `genericPoint` is the affine point of the base-changed curve $W \otimes$ `GenK (Fin 2) R` with coordinates $x = \iota(t)/\iota(w(t))$ and $y = -1/\iota(w(t))$. The theorem asserts the existence of the three non-vanishing facts $\iota(w(F)) \ne 0$, $\iota(w(X_0)) \ne 0$, $\iota(w(X_1)) \ne 0$, where $F =$ `formalGroupLawFixed` is the two-variable series obtained by substituting `fgZ3Fixed` into `fgInv`, together with the identity, in the Mathlib group of affine points of the base-changed curve,
--   $$\mathrm{gp}(F) = \mathrm{gp}(X_0) + \mathrm{gp}(X_1),$$
--   the substitutability of $F$, $X_0$ and $X_1$ being supplied by the vanishing of their constant coefficients.
--
--   This is the statement that the Weierstrass formal group law represents the chord–tangent addition on generic points, i.e. the series-theoretic half of the identification of the formal group of $W$ with the group law near the origin. It is used in the analysis of the multiplication-by-$n$ series (`nthSeries_ne_zero_and_not_X_pow_dvd_of_charP`) and in the comparison of the formal group law with the origin chart of the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_genericPoint_formalGroupLawFixed_eq_add.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve

open Classical in

theorem WeierstrassCurve.exists_genericPoint_formalGroupLawFixed_eq_add
    {R : Type} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ (hwF : WeierstrassCurve.genι (W.fgGenW W.formalGroupLawFixed) ≠ 0)
      (hw0 : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)) ≠ 0)
      (hw1 : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)) ≠ 0),
      W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalGroupLawFixed) hwF
        = W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)) hw0
          + W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)) hw1 := by sorry
