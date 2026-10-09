-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumUB_padded_roots_feasible
-- name    : SymPolyOpt.PowerSumUB.padded_roots_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:43.445245+00:00
-- url     : https://prove2.me/theorems/938f0907-1adc-4a83-86d7-c4f8c8d0d40f
-- title:
--   Proof of Theorem 6.7, p. 27 — the real roots of a feasible p, padded by zeros, are feasible for P_nmq
-- statement:
--   Let $m \le n$ and $q \ge 1$, and let $p$ be feasible for the SDP (6.7): $p$ is monic of degree $m$, $s_j(p) = \gamma_j$ for $j = 1, \dots, m-1$, and $H_m(s(p)) \succeq 0$. Suppose all roots $x_1, \dots, x_m$ of $p$ (with multiplicity) are real. Then there is a point $x^* \in \mathbb{R}^n$ feasible for $\mathrm{P}_{nmq}$, namely $x^* = (x_1, \dots, x_m, 0, \dots, 0)$, with
--   $$\sum_{i=1}^n (x^*_i)^q = s_q(p).$$
--
--   This is the construction in the proof of Theorem 6.7 that turns a feasible point of (6.7) into a feasible point of (6.4) with the same objective value, which gives $\min \mathrm{P}_{nmq} \le \mathrm{U}_{nmq}$.
--
--   **Formalization Note** The real-rootedness of $p$ is a hypothesis here; Hermite's criterion supplies it from $H_m(s) \succeq 0$. The hypothesis $q \ge 1$ is needed because the padding zeros contribute $0^q$, which is $1$ for $q = 0$; Theorem 6.7 has $q \ge m \ge 2$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 27, proof of Theorem 6.7

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

namespace SymPolyOpt.PowerSumUB

open Polynomial

theorem padded_roots_feasible (n m q : ℕ) (γ : ℕ → ℝ) (hmn : m ≤ n) (p : ℝ[X])
    (hp : p ∈ feasU m γ) (hreal : ∀ z ∈ p.aroots ℂ, z.im = 0) (hq : 1 ≤ q) :
    ∃ x ∈ SymPolyOpt.PowerSumLB.feasP n m γ, SymPolyOpt.PowerSumLB.powerSum x q = newtonSum p q := by sorry

end SymPolyOpt.PowerSumUB
