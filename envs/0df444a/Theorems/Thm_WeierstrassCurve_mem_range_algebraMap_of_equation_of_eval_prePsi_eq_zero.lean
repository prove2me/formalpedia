-- Prove2me | Theorems.Thm_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
-- name    : WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/0fa08e34-06a7-56a3-911d-be52159d8d6f
-- title:
--   Integrality of division-polynomial roots when n is invertible
-- statement:
--   Let $R$ be an integrally closed domain with fraction field $K$ (the fraction-field structure being given by an algebra map $\mathrm{algebraMap}\,R\,K$ making $K$ a fraction ring of $R$), let $W$ be a Weierstrass curve over $R$, and let $n$ be a natural number whose image in $R$ is a unit. Suppose $x, y \in K$ satisfy the affine Weierstrass equation of the base-changed curve $W \otimes_R K$, that is $y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ with the $a_i$ taken in $K$, and suppose moreover that $x$ is a root of the $n$-th pre-$\Psi$ division polynomial of $W \otimes_R K$, i.e. the evaluation at $x$ of $(W.\mathrm{map}\,(\mathrm{algebraMap}\,R\,K)).\mathrm{pre}\Psi\,n$ vanishes. Then both $x$ and $y$ lie in the image of $\mathrm{algebraMap}\,R\,K$, i.e. both coordinates of the point come from $R$. No hypothesis of non-degeneracy (non-vanishing discriminant) of $W$ is imposed, and $n$ is an arbitrary natural number whose image is a unit.
--
--   This is the elementary integrality statement for $n$-torsion points with $n$ invertible on the base: over an integrally closed domain, an affine point of a Weierstrass curve over the fraction field whose abscissa kills the $n$-th division polynomial already has coordinates in the base. It is used to propagate level structures (a $\Gamma(p)$- or $\Gamma_1$-type structure, or a cyclic subgroup scheme) from the generic fibre to the base, and is cited by [`ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map`](thm.html#ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map), [`ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map`](thm.html#ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map) and [`WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (x y : K) (hxy : (W.map (algebraMap R K)).toAffine.Equation x y)
    (hψ : ((W.map (algebraMap R K)).preΨ n).eval x = 0) :
    x ∈ Set.range (algebraMap R K) ∧ y ∈ Set.range (algebraMap R K) := by sorry
