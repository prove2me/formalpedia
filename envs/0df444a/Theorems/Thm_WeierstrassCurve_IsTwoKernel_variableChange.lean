-- Prove2me | Theorems.Thm_WeierstrassCurve_IsTwoKernel_variableChange
-- name    : WeierstrassCurve.IsTwoKernel.variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/7e4cba54-9f18-5534-b8a7-fd6717492b59
-- title:
--   Two-torsion kernel polynomials under Weierstrass changes of variables
-- statement:
--   Let $T$ be a commutative ring, $W$ a Weierstrass curve over $T$, and $C = (u,r,s,t)$ a Weierstrass change of variables over $T$ (so $u \in T^{\times}$). Let $h \in T[X]$ satisfy the predicate [`WeierstrassCurve.IsTwoKernel`](def/ModularCurve_WeierstrassGamma0Sqf.html#L22) for $W$, that is: $\deg h \le 1$, the coefficient of $X$ in $h$ equals $1$, and $h$ divides the squared $2$-division polynomial $W.\Psi_2^{\mathrm{Sq}} = 4X^3 + b_2X^2 + 2b_4X + b_6$ of $W$. The conclusion is that the transported polynomial $\mathrm{kernelVariableChangeDeg}\,C\,1\,h = u^{-2}\,h(u^{2}X + r)$ — in Lean, $\mathrm{C}((u^{-1})^{2\cdot 1}) \cdot h \circ (\mathrm{C}(u)^2 X + \mathrm{C}(r))$ — satisfies the same three conditions with respect to the transformed curve $C \bullet W$: its degree is at most $1$, its coefficient of $X$ is $1$, and it divides $(C \bullet W).\Psi_2^{\mathrm{Sq}}$. No invertibility of $2$ or of the discriminant is assumed, so the statement holds over any commutative ring, residue characteristic $2$ included.
--
--   This is the $\Gamma_0$-type compatibility of a linear factor of the squared $2$-division polynomial with the action of Weierstrass changes of variables: a choice of order-$2$ subgroup, encoded by a monic linear divisor of $\Psi_2^{\mathrm{Sq}}$, is carried to such a choice on the transformed curve. It supplies the $p^k = 2$ case of [`ModularCurve.IsGamma0PowAt.variableChange`](thm.html#ModularCurve.IsGamma0PowAt.variableChange), used when assembling level structures with even level along the modularity route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsTwoKernel_variableChange.lean

import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem WeierstrassCurve.IsTwoKernel.variableChange
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (h : Polynomial T) (hh : W.IsTwoKernel h) :
    (C • W).IsTwoKernel (ModularCurve.kernelVariableChangeDeg C 1 h) := by sorry
