-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
-- name    : WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/621f26ab-fe12-5b0a-b7c1-e9be300e13de
-- title:
--   Residual modularity mod 3 at a cube-free level, with inertia condition
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta \ne 0$ which is a semistable model in the project's sense, i.e. no prime dividing $\Delta$ also divides $c_4$, and suppose the project's predicate `ModRepIsIrreducible` holds for $W$ at $3$: the $3$-torsion subgroup $\mathrm{Submodule.torsionBy}\ \mathbb{Z}$ of the group of affine points of $W$ base-changed to $\overline{\mathbb{Q}}$ is nontrivial and has no $\mathbb{Z}/3$-submodule stable under all of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ other than $\bot$ and $\top$. The conclusion asserts the existence of a natural number $M > 0$ with three properties. First, $W$ is residually modular of level $M$ mod $3$ in the project's sense: there are a cusp form $f$ of weight $2$ on $\Gamma_0(M)$ which is a normalised eigenform (normalised first $q$-coefficient, multiplicativity at coprime indices, and the two Hecke recursions at prime powers according as the prime divides $M$ or not) and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $3$, such that for every prime $\ell$ not dividing $M$, distinct from $3$, and good for $W$ (i.e. $\ell \nmid \Delta$), the $\ell$-th $q$-coefficient of $f$ is the image of some algebraic integer $a$ with $a - a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ mod $\ell$. Second, the level is cube-free away from $3$: $q^3 \nmid M$ for every prime $q \ne 3$. Third, if $9 \mid M$, then for every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $3$ (meaning $3$ is a nonunit of $A$), every $3$-torsion point fixed by the whole image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ is zero.
--
--   This is the Langlands–Tunnell input to Wiles's proof, in the shape Wiles uses it: the mod-$3$ representation of a semistable curve with irreducible $\bar\rho_{W,3}$ is residually modular, with additional control on the level (cube-free away from $3$) and, in the case $9 \mid M$, on inertia at $3$ acting on $W[3]$. Compared with the textbook statement, residual modularity is packaged not as a congruence of Galois representations but as a congruence modulo a maximal ideal above $3$ between the $q$-coefficients of a normalised weight-$2$ eigenform on $\Gamma_0(M)$ and the Frobenius traces $a_\ell(W)$ at good primes $\ell \nmid M$, $\ell \ne 3$; the two side conditions are exactly what the modularity lifting theorems at $p = 3$ require. It is used in [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel) and, through it, in [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel.lean

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (h3 : W.ModRepIsIrreducible 3) :
    ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel 3 M ∧
      (∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ^ 3 ∣ M) ∧
      (3 ^ 2 ∣ M →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
          ∀ x : Submodule.torsionBy ℤ
              ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (3 : ℕ),
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0) := by sorry
