-- Prove2me | Theorems.Thm_PeriodPair_weierstrassP_scale
-- name    : PeriodPair.weierstrassP_scale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/3658afe4-1c80-5b44-a851-1ca86a73d459
-- title:
--   Homogeneity of wp under scaling of the period pair
-- statement:
--   Let $L$ be a period pair, i.e. a pair of complex numbers $\omega_1,\omega_2$ together with the independence condition recorded in the structure `PeriodPair`, let $\alpha$ be a unit of $\mathbb{C}$ (so a non-zero complex number, with its inverse), and let $z$ be an arbitrary complex number. Write `L.scale α` for the period pair with periods $\alpha\omega_1$ and $\alpha\omega_2$, whose independence is inherited from that of $L$, and write `PeriodPair.weierstrassP` for the Weierstrass $\wp$-function attached to a period pair. The assertion is the exact identity
--   $$\wp_{\alpha L}(\alpha z) \;=\; (\alpha^2)^{-1}\,\wp_L(z)$$
--   of complex numbers, valid for every $z$ without any hypothesis excluding the lattice points: no condition $z\notin \mathbb{Z}\omega_1+\mathbb{Z}\omega_2$ is imposed, the equality holding at the poles as well because inversion in $\mathbb{C}$ is the `Mathlib` total operation with $0^{-1}=0$. Here $(\alpha^2)^{-1}$ is the inverse of the square of the complex number underlying $\alpha$.
--
--   This is the classical homogeneity (weight $-2$) of the Weierstrass $\wp$-function under a homothety of the lattice, $\wp_{\alpha\Lambda}(\alpha z)=\alpha^{-2}\wp_\Lambda(z)$. It is used in [`CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq`](thm.html#CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq), where values of $\wp$ along a lattice are compared after rescaling the period pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_weierstrassP_scale.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PeriodPair.weierstrassP_scale (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by sorry
