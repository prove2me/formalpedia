-- Prove2me | Theorems.Thm_WeierstrassCurve_IsModularModelOfExactConductorLevel_isModularModelOfConductorLevel
-- name    : WeierstrassCurve.IsModularModelOfExactConductorLevel.isModularModelOfConductorLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/f94c97ab-7e43-5511-b65d-0ed0bc891ddc
-- title:
--   Exact-conductor modularity implies conductor-level modularity
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$. Assume `W.IsModularModelOfExactConductorLevel`, that is, [`Mlc1IsModularModelOfExactConductorLevel W`](def/WeierstrassCurve_Mlc1RowStatement.html#L9): there is a natural number $N$ with $N>0$, $N$ squarefree, such that for every prime $q$ one has $q \mid N$ if and only if $q$ divides the discriminant $W.\Delta$ in $\mathbb{Z}$, and such that $W$ is a modular model of level $N$ in the sense of `IsModularModelOfLevel`: there exists a cusp form $f$ of weight $2$ for the congruence subgroup $\Gamma_0(N)$ which is a normalised eigenform and whose $q$-expansion coefficient at each prime $p$ of good reduction for $W$ not dividing $N$ equals $a_p$ of the model, $(W.\mathrm{apOfModel}\ p : \mathbb{C})$. The conclusion is `W.IsModularModelOfConductorLevel`: there exists a natural number $N$ with $N>0$ such that $W$ is a modular model of level $N$ in the above sense and, for every prime $\ell$ dividing $W.\Delta$ in $\mathbb{Z}$, $\ell$ divides $N$. Thus only one direction of the divisibility equivalence, and no squarefreeness, is asserted in the conclusion.
--
--   This is the passage from the two-sided (exact) form of conductor-level modularity, in which the prime support of the level is exactly the set of primes of bad reduction and the level is squarefree, to the weaker one-sided form, in which every bad prime merely divides the level. It is the interface used by [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel), where the stronger form produced by the modularity lifting step is fed into arguments that require only the one-sided statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsModularModelOfExactConductorLevel_isModularModelOfConductorLevel.lean

import Definitions.Def_WeierstrassCurve_ModularityLiftingConductor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.IsModularModelOfExactConductorLevel.isModularModelOfConductorLevel
    {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfExactConductorLevel) : W.IsModularModelOfConductorLevel := by sorry
