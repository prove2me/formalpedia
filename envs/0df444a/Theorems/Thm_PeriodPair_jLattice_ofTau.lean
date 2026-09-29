-- Prove2me | Theorems.Thm_PeriodPair_jLattice_ofTau
-- name    : PeriodPair.jLattice_ofTau
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e347fa49-29e8-5478-bedd-7d8c08d463f9
-- title:
--   Lattice j-invariant of ℤτ+ℤ equals E₄³/Δ
-- statement:
--   Let $\tau$ be a point of the upper half-plane $\mathbb{H}$. Associated with $\tau$ is the period pair [`PeriodPair.ofTau τ`](def/PeriodPair_Uniformization.html#L104) with $\omega_1 = \tau$, $\omega_2 = 1$, the required $\mathbb{R}$-linear independence of the pair $(\tau, 1)$ in $\mathbb{C}$ being supplied by the fact that $\tau$ has nonzero imaginary part; the associated lattice is thus $\Lambda_\tau = \mathbb{Z}\tau + \mathbb{Z}$. For a period pair $L$ the quantity `jLattice` is defined to be the complex number $1728\,g_2(L)^3/\bigl(g_2(L)^3 - 27\,g_3(L)^2\bigr)$, where $g_2$ and $g_3$ are the Weierstrass invariants of $L$. The theorem asserts the equality in $\mathbb{C}$ $$\mathrm{jLattice}(\Lambda_\tau) \;=\; \frac{E_4(\tau)^3}{\Delta(\tau)},$$ where $E_4$ is Mathlib's normalised weight-four level-one Eisenstein series `ModularForm.E₄` and $\Delta$ is Mathlib's modular discriminant `ModularForm.discriminant`. No hypothesis beyond $\tau \in \mathbb{H}$ is imposed: both sides are quotients formed with the field division of $\mathbb{C}$, and the relevant denominators are in fact nonzero.
--
--   This is the classical identification of the $j$-invariant of the lattice $\mathbb{Z}\tau + \mathbb{Z}$, formed from the Weierstrass invariants $g_2, g_3$, with the value at $\tau$ of the modular function $j = E_4^3/\Delta$. It links the lattice-theoretic uniformisation theory to the analytic, $q$-expansion side, and is used in the proof that `jLattice` of a lattice with cyclic quotient is a root of the relevant modular polynomial, via [`ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic`](thm.html#ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_jLattice_ofTau.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped UpperHalfPlane

theorem PeriodPair.jLattice_ofTau (τ : ℍ) :
    (PeriodPair.ofTau τ).jLattice = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by sorry
