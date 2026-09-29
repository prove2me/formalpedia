-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range
-- name    : WeierstrassCurve.exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/84e9097f-fc2f-5b28-8008-bda782238fdc
-- title:
--   Good integral model over a DVR from a Γ₁(ℓ)-point and integral j
-- statement:
--   Let $R_0$ be a discrete valuation ring which is a domain, with fraction field $K$ (both in the same universe, $K$ a field with an $R_0$-algebra structure making it the fraction field). Let $\ell$ be a prime with $\ell \ge 5$ whose image in $R_0$ is a unit, and let $W$ be a Weierstrass curve over $K$ whose discriminant $W.\Delta$ is a unit of $K$; write $W.j$ for its $j$-invariant, formed using the elliptic structure supplied by that unit hypothesis, and assume $W.j$ lies in the image of $\mathrm{algebraMap}\,R_0\,K$. Finally let $D$ be a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $K$ (a [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43)) such that [`ModularCurve.IsGamma1Point W ℓ D`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) holds, i.e. $(x_P,y_P)$ satisfies the affine Weierstrass equation of $W$, the polynomial $W.\mathrm{pre}\Psi\,\ell$ vanishes at $x_P$, and $x_Q = x_P$, $y_Q = y_P$ (so the datum records a single affine point annihilated by the $\ell$-division polynomial factor). The conclusion asserts the existence of a Weierstrass variable change $C$ over $K$ and a Weierstrass curve $W_0$ over $R_0$ whose discriminant is a unit of $R_0$, such that $C \bullet W$ equals the base change of $W_0$ along $\mathrm{algebraMap}\,R_0\,K$.
--
--   This is the potentially-good-reduction criterion in its $\Gamma_1(\ell)$ form: a curve over the fraction field of a discrete valuation ring with integral $j$-invariant and a point killed by the $\ell$-division polynomial, $\ell \ge 5$ invertible, already has a model with unit discriminant over the ring itself, with no hypothesis on the invertibility of $2$ and $3$. It feeds the analysis of the $H_1$-type moduli data over the $j$-line, being cited in the proofs of [`ModularCurve.FullLevel.Diamond.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_rigidDataH1Pow) and [`ModularCurve.FullLevel.Diamond.isIntegral_adjoin_j0_levelModuliPackageAbs_trivial_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.isIntegral_adjoin_j0_levelModuliPackageAbs_trivial_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
    (hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K))
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    ∃ (C : WeierstrassCurve.VariableChange K) (W₀ : WeierstrassCurve R₀),
      IsUnit W₀.Δ ∧ C • W = W₀.map (algebraMap R₀ K) := by sorry
