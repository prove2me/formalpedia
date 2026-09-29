-- Prove2me | Theorems.Thm_WeierstrassCurve_isModular_map_of_isModularModel
-- name    : WeierstrassCurve.isModular_map_of_isModularModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/706f6911-3414-519c-a9f1-1133d89ab0f9
-- title:
--   Modularity of a curve from a modular integral model
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, and assume $W$ satisfies `IsModularModel`: there is a natural number $N>0$ together with a cusp form $f$ of weight $2$ for the congruence subgroup $\Gamma_0(N)$ which is a normalised eigenform and whose $p$-th $q$-expansion coefficient equals the image in $\mathbb{C}$ of $W.\mathrm{apOfModel}\,p$ for every prime $p$ that is a good prime for $W$ and does not divide $N$. The conclusion is that the Weierstrass curve $W.\mathrm{map}(\mathrm{Int.castRingHom}\ \mathbb{Q})$ over $\mathbb{Q}$, obtained by base change along $\mathbb{Z}\to\mathbb{Q}$, satisfies `IsModular`: there exists a Weierstrass curve $W'$ over $\mathbb{Z}$ which is an integral model of it, in the sense that some Weierstrass variable change $C$ over $\mathbb{Q}$ carries $W.\mathrm{map}(\mathrm{Int.castRingHom}\ \mathbb{Q})$ to $W'.\mathrm{map}(\mathrm{Int.castRingHom}\ \mathbb{Q})$, and which is itself a modular model in the above sense.
--
--   This is the passage from the model-level formulation of modularity (an integral Weierstrass equation whose good-prime traces are matched by a normalised weight-two eigenform of some level) to the curve-level formulation for the base-changed curve over $\mathbb{Q}$, which quantifies over integral models up to a rational change of variables. It is used in the assembly of the modularity statement for semistable models, [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isModular_map_of_isModularModel.lean

import Definitions.Def_WeierstrassCurve_ModularityProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isModular_map_of_isModularModel {W : WeierstrassCurve ℤ} (h : W.IsModularModel) :
    (W.map (Int.castRingHom ℚ)).IsModular := by sorry
