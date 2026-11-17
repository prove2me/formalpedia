-- Prove2me | Theorems.Thm_RandomInvolutions_norm_sum_c2count_mul_trace_Bprod_le
-- name    : RandomInvolutions.norm_sum_c2count_mul_trace_Bprod_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T11:46:12.651602+00:00
-- url     : https://prove2.me/theorems/f23d4a9f-d200-4823-a352-ef568ab6c41f
-- title:
--   Linearized moment bound for the two-fixed-point words of Z₂^{*r}
-- statement:
--   Let $L$ be a linearization datum over $\Gamma_r = \mathbb Z_2^{*r}$ (`BordenaveCollins.Lin 0 r`) whose linear factors have operator norm $\|X_j\| \le R$ in the regular representation. Then for all $i_0, j_0$ there are $C$ and $k$ such that for all $m \ge 1$
--   $$\Big\|\sum_{\iota : \mathrm{Fin}\, m \to \mathrm{Option}(\text{letters})} \mathrm{C2count}_{i_0 j_0}(\iota_1 \cdots \iota_m)\, \operatorname{tr}\, B_m(\iota)\Big\| \le C\, m^k R^m.$$
--   Here $\mathrm{C2count}_{i_0 j_0}(g)$ counts the reduced representations $g = a\,(b\, m_{j_0} b^{-1}\, c\, m_{i_0} c^{-1})^k a^{-1}$, $k \ge 1$, and $B_m(\iota)$ is as in `BordenaveCollins.Bprod`. It gives the growth of the moments of the term of the trace expansion that is quadratic in the numbers of fixed points: two fixed points joined by a path, traversed back and forth.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 28-29, Lemmas 9.5 and 9.6, for the two-loop words of Z_2^{*r}; a step of our proof of the strong convergence of uniform random involutions (the case Γ = Z_2^{*r} of Barbieri, M. and Jezernik, U., Strong convergence of random representations of free products of finite groups, arXiv:2602.11905 (2026), https://arxiv.org/abs/2602.11905)

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_RandomInvolutions

open BordenaveCollins

namespace RandomInvolutions

theorem norm_sum_c2count_mul_trace_Bprod_le {r : ℕ} (L : Lin 0 r) (R : ℝ) (hR : 0 ≤ R) (hX : ∀ j, ‖Xop L j‖ ≤ R)
    (i0 j0 : Fin r) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt 0 r), (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  sorry

end RandomInvolutions
