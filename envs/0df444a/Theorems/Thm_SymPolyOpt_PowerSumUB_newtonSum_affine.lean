-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumUB_newtonSum_affine
-- name    : SymPolyOpt.PowerSumUB.newtonSum_affine
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:10.039395+00:00
-- url     : https://prove2.me/theorems/377fade3-e494-4d22-8a81-8a874ca93125
-- title:
--   §6.2, p. 27 — Q_j(p_0) is affine in p_0 whenever m ≤ j ≤ 2m − 1
-- statement:
--   Fix $m$ and real numbers $\gamma_1, \dots, \gamma_{m-1}$, and consider the monic real polynomials $p$ of degree $m$ whose Newton sums satisfy $s_i(p) = \gamma_i$ for $i = 1, \dots, m-1$. For every $j$ with $m \le j \le 2m-1$ there are real constants $a, b$ (depending on $m$, $\gamma$ and $j$ only) such that for all such $p$,
--   $$s_j(p) = a + b\, p_0,$$
--   where $p_0$ is the constant coefficient of $p$. In the paper's notation, $s_j = Q_j(p_0)$ with $Q_j$ affine for $j \le 2m - 1$.
--
--   This is what makes (6.7) a semidefinite program: the entries $s_m, \dots, s_{2m-2}$ of the Hankel matrix $H_m(s)$ and the objective $s_q$, $q \le 2m-2$, are affine functions of the single variable $p_0$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 27, §6.2, "We claim that Q_j is affine whenever j ≤ 2m−1."

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

namespace SymPolyOpt.PowerSumUB

open Polynomial

theorem newtonSum_affine (m : ℕ) (γ : ℕ → ℝ) (j : ℕ) (hmj : m ≤ j) (hj : j ≤ 2 * m - 1) :
    ∃ a b : ℝ, ∀ p : ℝ[X], p.Monic → p.natDegree = m →
      (∀ i : ℕ, 1 ≤ i → i ≤ m - 1 → newtonSum p i = γ i) →
        newtonSum p j = a + b * p.coeff 0 := by sorry

end SymPolyOpt.PowerSumUB
