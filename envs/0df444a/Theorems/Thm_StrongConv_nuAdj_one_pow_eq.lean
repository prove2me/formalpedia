-- Prove2me | Theorems.Thm_StrongConv_nuAdj_one_pow_eq
-- name    : StrongConv.nuAdj_one_pow_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:49:54.555395+00:00
-- url     : https://prove2.me/theorems/89712b33-f7b6-4b08-a9fa-c27486f71a2e
-- title:
--   Lemma 8.2 — the moments of ν₁ for random regular graphs
-- statement:
--   For every $d$ and $p \ge 1$, the first-order coefficient $\nu_1$ of the expansion of $\mathbf E[\mathrm{tr}_N\, h(A^N)]$ in powers of $1/N$ (`nuAdj d 1`) satisfies
--   $$\nu_1(x^p) = -\tau(A_{\rm F}^p) + \sum_{k=2}^p (\omega(k) - 1)\,\#\big\{(i_1, \dots, i_p, v) : v \in \mathbf F_d^{\rm np},\ g_{i_1}\cdots g_{i_p} = v^k\big\},$$
--   where $i_1, \dots, i_p$ range over the $2d$ letters $g_1, \dots, g_d, g_1^{-1}, \dots, g_d^{-1}$, $\omega(k)$ is the number of divisors of $k$, $\mathbf F_d^{\rm np}$ is the set of non-powers, and $\tau(A_{\rm F}^p)$ is taken as a real number (its real part). The double sum of indicators is written as the number of pairs $(i, v)$; for each $i$ there is at most one such $v$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 24, Lemma 8.2

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem nuAdj_one_pow_eq (d p : ℕ) (hp : 1 ≤ p) :
    nuAdj d 1 (X ^ p) = -(tau (adjFree d ^ p)).re +
      ∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
        Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
          IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} := by
  sorry

end StrongConv
