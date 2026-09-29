-- Prove2me | Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_variableChange
-- name    : WeierstrassCurve.IsCyclicGenKernel.variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e9115a8c-530c-5970-af96-9ce1dcade77d
-- title:
--   Generator-kernel polynomials of level p^k under variable change
-- statement:
--   Let $T$ be a commutative ring, $W$ a Weierstrass curve over $T$, and $C = (u,r,s,t)$ a Weierstrass variable change over $T$; let $p,k$ be natural numbers and $h \in T[X]$. Put $d = \varphi(p^k)/2$ (integer division). Assume `W.IsCyclicGenKernel p k h`, that is: $\deg h \le d$; the coefficient of $X^d$ in $h$ equals $1$; $h \cdot W.\mathrm{pre}\Psi(p^{k-1})$ divides $W.\mathrm{pre}\Psi(p^{k})$, the exponent $k-1$ being truncated natural subtraction; and for every natural $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$, the polynomial $h$ divides $W.\mathrm{smulNumerator}\,a\,d\,h = \sum_{i=0}^{d} h_i \,\Phi_a^{\,i}\,\Psi_a^{2(d-i)}$, where $h_i$ is the $i$-th coefficient of $h$ and $\Phi_a, \Psi_a^2$ are the $a$-division polynomials of $W$. The conclusion is that the transformed curve $C \bullet W$ satisfies `IsCyclicGenKernel p k` for the polynomial $\mathrm{kernelVariableChangeDeg}\,C\,d\,h = u^{-2d}\, h(u^2X + r)$, i.e. all four clauses above hold with $W$ replaced by $C \bullet W$, with $h$ replaced by this polynomial, and with the same $p$, $k$ and hence the same $d$.
--
--   This is the statement that the datum of a cyclic-subgroup-of-order-$p^k$ kernel polynomial, in the form used for the Weierstrass model of $\Gamma_0(p^k)$-structures, is transported by an isomorphism of Weierstrass models, the kernel polynomial being rescaled and composed with $u^2X+r$. It is used by [`ModularCurve.IsGamma0PowAt.variableChange`](thm.html#ModularCurve.IsGamma0PowAt.variableChange) and by the comparison of the transported kernel polynomials with images of cyclic subgroups under the isomorphism, [`ModularCurve.forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq`](thm.html#ModularCurve.forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsCyclicGenKernel_variableChange.lean

import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem WeierstrassCurve.IsCyclicGenKernel.variableChange
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (p k : ℕ)
    (h : Polynomial T) (hh : W.IsCyclicGenKernel p k h) :
    (C • W).IsCyclicGenKernel p k (ModularCurve.kernelVariableChangeDeg C (Nat.totient (p ^ k) / 2) h) := by sorry
