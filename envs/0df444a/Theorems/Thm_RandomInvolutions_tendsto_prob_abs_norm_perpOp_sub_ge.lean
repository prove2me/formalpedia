-- Prove2me | Theorems.Thm_RandomInvolutions_tendsto_prob_abs_norm_perpOp_sub_ge
-- name    : RandomInvolutions.tendsto_prob_abs_norm_perpOp_sub_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T11:46:26.810629+00:00
-- url     : https://prove2.me/theorems/15be19d1-0ed3-4dbc-ab21-a4190d1a57f4
-- title:
--   Strong convergence of uniform random involutions, with matrix coefficients
-- statement:
--   Let $\tau_1, \dots, \tau_r$ be independent uniform involutions of $\{0, \dots, N-1\}$ (fixed points allowed). For every $D$, every $x = \sum_g x_g\, g \in M_D(\mathbb C)[\Gamma_r]$ with $\Gamma_r = \mathbb Z_2^{*r}$, and every $\varepsilon > 0$,
--   $$\Pr\Big[\,\big|\|\mathrm{perpOp}(\tau, x)\| - \|\lambda(x)\|\big| \ge \varepsilon\Big] \longrightarrow 0 \qquad (N \to \infty),$$
--   where $\mathrm{perpOp}(\tau, x) = (I \otimes Q)\big(\sum_g x_g \otimes P_{g(\tau)}\big)(I \otimes Q)$ is $x$ in the permutation representation compressed to the complement of the constants, and $\lambda(x)$ is $x$ in the left-regular representation on $D$ copies of $\ell^2(\Gamma_r)$ (`regOp`).
--
--   This is the case $\Gamma = \mathbb Z_2^{*r}$ of Theorem 1.1 of Barbieri and Jezernik, *Strong convergence of random representations of free products of finite groups* (arXiv:2602.11905), with matrix coefficients. Our proof is different: it conditions on the numbers of fixed points and uses the polynomial method of Chen, Garza-Vargas, Tropp and van Handel at second order.
-- source:
--   Barbieri, M. and Jezernik, U., Strong convergence of random representations of free products of finite groups, arXiv:2602.11905 (2026), https://arxiv.org/abs/2602.11905, Theorem 1.1 for Γ = Z_2^{*r}, with matrix coefficients; proved by the polynomial method of Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used) after conditioning on the numbers of fixed points

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_StrongConv
import Definitions.Def_RandomInvolutions

open Filter Topology BordenaveCollins

namespace RandomInvolutions

theorem tendsto_prob_abs_norm_perpOp_sub_ge {r : ℕ} {D : ℕ} (x : MG D 0 r) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb
      (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ε ≤ |‖perpOp (homI τ) x‖ - ‖regOp x‖|)) atTop (𝓝 0) := by
  sorry

end RandomInvolutions
