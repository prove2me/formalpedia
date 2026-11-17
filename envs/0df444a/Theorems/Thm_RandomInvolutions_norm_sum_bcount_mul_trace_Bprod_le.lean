-- Prove2me | Theorems.Thm_RandomInvolutions_norm_sum_bcount_mul_trace_Bprod_le
-- name    : RandomInvolutions.norm_sum_bcount_mul_trace_Bprod_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T11:46:17.293922+00:00
-- url     : https://prove2.me/theorems/eeca428b-62f1-4eb6-8008-f3255cafe6a9
-- title:
--   Linearized moment bound for the conjugates of the generators of Z₂^{*r}
-- statement:
--   Let $L$ be a linearization datum over $\Gamma_r = \mathbb Z_2^{*r}$ (`BordenaveCollins.Lin 0 r`) whose linear factors have operator norm $\|X_j\| \le R$ in the regular representation. Then for each $i_0$ there are $C$ and $k$ such that for all $m \ge 1$
--   $$\Big\|\sum_{\iota : \mathrm{Fin}\, m \to \mathrm{Option}(\text{letters})} \mathrm{Bcount}_{i_0}(\iota_1 \cdots \iota_m)\, \operatorname{tr}\, B_m(\iota)\Big\| \le C\, m^k R^m.$$
--   Here $\mathrm{Bcount}_{i_0}(g)$ is the number of reduced conjugates $g = a\, m_{i_0}\, a^{-1}$, and $B_m(\iota)$ is the matrix product of the factors' coefficients along $\iota$ (`Bprod`). It gives the growth of the moments of the single-fixed-point term in the trace expansion of random involutions.
--
--   It is the involution analogue of `BordenaveCollins.norm_sum_cfun_mul_trace_Bprod_le`, by the first-passage method of Chen, Garza-Vargas, Tropp and van Handel (Lemmas 9.4–9.6).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 28-29, Lemmas 9.5 and 9.6, for the conjugates of the generators of Z_2^{*r}; a step of our proof of the strong convergence of uniform random involutions (the case Γ = Z_2^{*r} of Barbieri, M. and Jezernik, U., Strong convergence of random representations of free products of finite groups, arXiv:2602.11905 (2026), https://arxiv.org/abs/2602.11905)

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_RandomInvolutions

open BordenaveCollins

namespace RandomInvolutions

theorem norm_sum_bcount_mul_trace_Bprod_le {r : ℕ} (L : Lin 0 r) (R : ℝ) (hR : 0 ≤ R) (hX : ∀ j, ‖Xop L j‖ ≤ R)
    (i0 : Fin r) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt 0 r), (Bcount i0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  sorry

end RandomInvolutions
