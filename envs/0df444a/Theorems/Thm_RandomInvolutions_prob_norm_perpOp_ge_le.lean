-- Prove2me | Theorems.Thm_RandomInvolutions_prob_norm_perpOp_ge_le
-- name    : RandomInvolutions.prob_norm_perpOp_ge_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T11:46:24.550653+00:00
-- url     : https://prove2.me/theorems/96863127-9df8-4336-91eb-5d7e87f2190c
-- title:
--   Upper tail of the norm for involutions with prescribed fixed-point counts, uniformly in the counts
-- statement:
--   Let $D \ge 1$ and let $z = \sum_g z_g\, g$ be a self-adjoint element of $M_D(\mathbb C)[\Gamma_r]$, $\Gamma_r = \mathbb Z_2^{*r}$, and $\varepsilon > 0$. There is $C$ such that for all $N \ge 1$ and all $\kappa$ with $N$ admissible (`AdmK N κ`), if $\tau = (\tau_i)$ is uniform in `OmK r N κ` (independent involutions with exactly $\kappa_i$ fixed points), then
--   $$\Pr\big[\|\mathrm{perpOp}(\tau, z)\| \ge \|\lambda(z)\| + \varepsilon\big] \le C\,\frac{\ell(\kappa)}{N} + C\,\frac{\ell(\kappa)^3}{N^2}, \qquad \ell(\kappa) = 1 + \sum_i \kappa_i,$$
--   where $\mathrm{perpOp}(\tau, z)$ is $z$ in the permutation representation compressed to the complement of the constants, and $\lambda(z)$ is the regular representation (`regOp`). The bound tends to $0$ uniformly over $\ell(\kappa) \le C'\sqrt N$, the typical size of the fixed-point counts of uniform involutions.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 9-10, Theorem 3.9 (upper bound), for involutions with prescribed numbers of fixed points; a step of our proof of the strong convergence of uniform random involutions (the case Γ = Z_2^{*r} of Barbieri, M. and Jezernik, U., Strong convergence of random representations of free products of finite groups, arXiv:2602.11905 (2026), https://arxiv.org/abs/2602.11905)

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_StrongConv
import Definitions.Def_RandomInvolutions

open BordenaveCollins

namespace RandomInvolutions

theorem prob_norm_perpOp_ge_le {r : ℕ} {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (N : ℕ) (κ : Fin r → ℕ), AdmK N κ → 1 ≤ N →
      StrongConv.uniformProb (fun τ : OmK r N κ => ‖regOp z‖ + ε ≤ ‖perpOp (homK τ) z‖) ≤
        C * lam κ / N + C * lam κ ^ 3 / (N : ℝ) ^ 2 := by
  sorry

end RandomInvolutions
