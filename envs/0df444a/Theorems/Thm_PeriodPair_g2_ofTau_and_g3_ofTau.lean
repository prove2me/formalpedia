-- Prove2me | Theorems.Thm_PeriodPair_g2_ofTau_and_g3_ofTau
-- name    : PeriodPair.g2_ofTau_and_g3_ofTau
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/fc0b4b30-82f0-5073-a2cc-36682770d292
-- title:
--   Lattice invariants of ℤτ+ℤ in terms of E₄, E₆
-- statement:
--   Let $\tau$ be a point of the upper half-plane `UpperHalfPlane`. Attached to it is the period pair [`PeriodPair.ofTau τ`](def/PeriodPair_Uniformization.html#L104), whose first period $\omega_1$ is $\tau$ regarded as a complex number and whose second period $\omega_2$ is $1$, the required independence being the $\mathbb{R}$-linear independence of the pair $(\tau, 1)$ in $\mathbb{C}$. The theorem asserts a conjunction of two identities in $\mathbb{C}$ for the invariants `g₂` and `g₃` of this period pair, that is, for the weight-$4$ and weight-$6$ invariants of the lattice $\mathbb{Z}\tau + \mathbb{Z}$: first, $g_2(\mathbb{Z}\tau+\mathbb{Z}) = 120\,\zeta(4)\,E_4(\tau)$, and second, $g_3(\mathbb{Z}\tau+\mathbb{Z}) = 280\,\zeta(6)\,E_6(\tau)$. Here $\zeta$ is the Riemann zeta function `riemannZeta`, evaluated at the complex arguments $4$ and $6$, and $E_4$, $E_6$ are the level-one Eisenstein series `ModularForm.E₄` and `ModularForm.E₆` of weights $4$ and $6$, normalised to constant term $1$.
--
--   This is the bridge between the Weierstrass invariants of a normalised lattice $\mathbb{Z}\tau+\mathbb{Z}$ and the level-one Eisenstein series of weights $4$ and $6$; since $\zeta(4)=\pi^4/90$ and $\zeta(6)=\pi^6/945$ are nonzero, it in particular converts vanishing statements for $g_2$, $g_3$ into vanishing statements for $E_4$, $E_6$. It is used in the proof of [`ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq`](thm.html#ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_g2_ofTau_and_g3_ofTau.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PeriodPair.g2_ofTau_and_g3_ofTau (τ : UpperHalfPlane) :
    (PeriodPair.ofTau τ).g₂ = 120 * riemannZeta 4 * ModularForm.E₄ τ ∧
      (PeriodPair.ofTau τ).g₃ = 280 * riemannZeta 6 * ModularForm.E₆ τ := by sorry
