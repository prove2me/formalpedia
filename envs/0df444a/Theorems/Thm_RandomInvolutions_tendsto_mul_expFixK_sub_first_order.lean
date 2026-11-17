-- Prove2me | Theorems.Thm_RandomInvolutions_tendsto_mul_expFixK_sub_first_order
-- name    : RandomInvolutions.tendsto_mul_expFixK_sub_first_order
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T11:46:26.860215+00:00
-- url     : https://prove2.me/theorems/ff7bd4b2-bfa0-434c-b052-743abc629fc8
-- title:
--   Second-order expansion of the expected fixed points of a word in involutions with prescribed fixed-point counts
-- statement:
--   Let $\tau_1, \dots, \tau_r$ be independent, with $\tau_i$ uniform among the involutions of $\{0, \dots, N-1\}$ with exactly $\kappa_i$ fixed points. For $g \ne 1$ in $\Gamma_r = \mathbb Z_2^{*r}$, let $\mathbb E_{N,\kappa}[\#\mathrm{fix}\, g(\tau)]$ be `expFixK r N κ g`. There are functions $C_0$ and $C_{1,i}$ on $\Gamma_r$, independent of $\kappa$, such that for every $\kappa$ and every $g \ne 1$, along admissible $N \to \infty$ (`admF κ`),
--   $$N\Big(\mathbb E_{N,\kappa}[\#\mathrm{fix}\, g(\tau)] - \mathrm{cfun}(g) - 1 - \sum_i \kappa_i\, \mathrm{Bcount}_i(g)\Big) \longrightarrow C_0(g) + \sum_i \kappa_i C_{1,i}(g) + \sum_{i,j} \kappa_i \kappa_j\, \mathrm{C2count}_{ij}(g).$$
--   Here $\mathrm{cfun}$ is the first-order function `BordenaveCollins.cfun` of the perfect-matching model, the case $\kappa = 0$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 19-20, Lemmas 5.1 and 5.2, for involutions with prescribed numbers of fixed points, to second order; a step of our proof of the strong convergence of uniform random involutions (the case Γ = Z_2^{*r} of Barbieri, M. and Jezernik, U., Strong convergence of random representations of free products of finite groups, arXiv:2602.11905 (2026), https://arxiv.org/abs/2602.11905)

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_RandomInvolutions

open Filter Topology BordenaveCollins

namespace RandomInvolutions

theorem tendsto_mul_expFixK_sub_first_order (r : ℕ) : ∃ (C0 : G 0 r → ℝ) (C1 : Fin r → G 0 r → ℝ),
    ∀ g : G 0 r, g ≠ 1 → ∀ κ : Fin r → ℕ,
      Tendsto (fun N : ℕ => (N : ℝ) * (expFixK r N κ g -
          ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) (admF κ)
        (𝓝 (C0 g + ∑ i, (κ i : ℝ) * C1 i g +
          ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)) := by
  sorry

end RandomInvolutions
