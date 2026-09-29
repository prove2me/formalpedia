-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
-- name    : WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/1fb4856b-a078-5e17-875c-9568ae3cecd2
-- title:
--   Good integral model from integral j and level-ℓ data
-- statement:
--   Let $R_0$ be a discrete valuation domain with fraction field $K$, and suppose that $2$ and $3$ are units in $R_0$. Let $\ell$ be a prime with $\ell \ge 3$ which is also a unit in $R_0$. Let $W$ be a Weierstrass curve over $K$ whose discriminant $\Delta(W)$ is a unit, so that $W$ is elliptic and its $j$-invariant $\mathrm{jOfUnit}$ is defined, and assume that this $j$-invariant lies in the image of $R_0 \to K$. Let $D$ be a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $K$ (a [`ModularCurve.LevelPData K`](def/ModularCurve_KatzLevelP.html#L43)) which is a level-$\ell$ structure on $W$ in the sense of [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104): both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, the division polynomial $W.\mathrm{pre\Psi}\,\ell$ vanishes at $x_P$ and at $x_Q$, and the two independence elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q = \prod_{a=1}^{(\ell-1)/2}\bigl(x_Q \cdot (W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units. Then there exist a Weierstrass variable change $C$ over $K$ and a Weierstrass curve $W_0$ over $R_0$ such that $\Delta(W_0)$ is a unit of $R_0$ and $C \cdot W$ equals the base change of $W_0$ along $R_0 \to K$.
--
--   This is the descent step behind good reduction over a discrete valuation ring: integrality of $j$ (with $6$ invertible) gives potential good reduction, and the presence of a full level-$\ell$ structure over $K$ for $\ell \ge 3$ forces the good model to be defined over $R_0$ itself rather than over an extension. It is used in the construction of integral models with full level structure, in [`ModularCurve.FullLevel.exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_levelModuliPackageAbs_trivial_of_isUnit_two_three_gamma0Pow) and [`ModularCurve.FullLevel.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_map_eq_of_isDiscreteValuationRing_of_jOf_mem_range_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
    (hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K))
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    ∃ (C : WeierstrassCurve.VariableChange K) (W₀ : WeierstrassCurve R₀),
      IsUnit W₀.Δ ∧ C • W = W₀.map (algebraMap R₀ K) := by sorry
