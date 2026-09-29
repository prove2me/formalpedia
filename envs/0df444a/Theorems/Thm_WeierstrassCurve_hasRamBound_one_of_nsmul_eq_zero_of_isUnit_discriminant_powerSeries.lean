-- Prove2me | Theorems.Thm_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
-- name    : WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/4bc78d56-a5e5-547d-9853-2d36912c5bdf
-- title:
--   Torsion coordinates of a good-reduction model are Laurent
-- statement:
--   Let $E$ be a Weierstrass curve over the power series ring $\overline{\mathbb Q}[[t]] =$ `PowerSeries (AlgebraicClosure ℚ)` whose discriminant $\Delta_E$ is a unit in that ring, and let $d$ be a natural number with $0 < d$. Consider the base change of $E$ along the inclusion `HahnSeries.ofPowerSeries` of $\overline{\mathbb Q}[[t]]$ into the Hahn series field $\overline{\mathbb Q}((t^{\mathbb Q}))$ of series with rational exponents and coefficients in $\overline{\mathbb Q}$, and let $x, y \in \overline{\mathbb Q}((t^{\mathbb Q}))$ be such that $(x,y)$ is a nonsingular point of the associated affine curve, so that it determines a point `WeierstrassCurve.Affine.Point.some x y h` of the group of points of that affine curve. Assume this point is killed by $d$, i.e. $d$ times it is the point at infinity. The conclusion is that both $x$ and $y$ satisfy [`HahnSeries.HasRamBound 1`](def/HahnSeries_RamificationBound.html#L32), that is, the support of each of $x$ and $y$ — its set of exponents with nonzero coefficient — is contained in the image of $k \mapsto (k : \mathbb Q)/1$ for $k \in \mathbb Z$, hence consists of integers; equivalently $x$ and $y$ lie in the Laurent subfield $\overline{\mathbb Q}((t))$.
--
--   This is the Néron–Ogg–Shafarevich phenomenon in the shape needed here: torsion points of a Weierstrass model with unit discriminant over the strictly Henselian ring $\overline{\mathbb Q}[[t]]$ acquire no ramification, so their coordinates have integral exponents. It is the base case for the ramification bounds attached to modular polynomial data, being used by the lemmas [`ModularCurve.ModularPolynomialData.hasRamBound_one_of_isRoot_off_zero_1728_of_odd`](thm.html#ModularCurve.ModularPolynomialData.hasRamBound_one_of_isRoot_off_zero_1728_of_odd), [`ModularCurve.ModularPolynomialData.hasRamBound_three_of_isRoot_at_zero_of_odd`](thm.html#ModularCurve.ModularPolynomialData.hasRamBound_three_of_isRoot_at_zero_of_odd) and [`ModularCurve.ModularPolynomialData.hasRamBound_two_of_isRoot_at_1728_of_odd`](thm.html#ModularCurve.ModularPolynomialData.hasRamBound_two_of_isRoot_at_1728_of_odd), which treat the elliptic points $j = 0$ and $j = 1728$ separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
    (E : WeierstrassCurve (PowerSeries (AlgebraicClosure ℚ))) (hΔ : IsUnit E.Δ) {d : ℕ} (hd : 0 < d)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] (x y : HahnSeries ℚ (AlgebraicClosure ℚ))
    (h : (E.map (HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular x y)
    (htor : d • (WeierstrassCurve.Affine.Point.some x y h :
      (E.map (HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ))).toAffine.Point) = 0) :
    HahnSeries.HasRamBound 1 x ∧ HahnSeries.HasRamBound 1 y := by sorry
