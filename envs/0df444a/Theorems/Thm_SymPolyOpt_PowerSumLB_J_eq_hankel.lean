-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumLB_J_eq_hankel
-- name    : SymPolyOpt.PowerSumLB.J_eq_hankel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:09.289496+00:00
-- url     : https://prove2.me/theorems/d29c4bdd-8b32-4071-ab2c-22fe5974c56c
-- title:
--   §6.2, p. 26 — for π_j = s_j / j the matrix J(z) is the Hankel matrix H_n(s) of power sums
-- statement:
--   Let $s_j = \sum_{i=1}^n X_i^{\,j}$ be the power sums in $\mathbb R[X_1,\dots,X_n]$ and $\pi_j = \tfrac1j s_j$ for $1 \le j \le n$. Then the matrix $J$ of (6.1),
--   $$J = \Big(\sum_{k=1}^n \frac{\partial \pi_i}{\partial X_k}\,\frac{\partial \pi_j}{\partial X_k}\Big)_{1\le i,j\le n},$$
--   is the Hankel matrix of power sums:
--   $$J = H_n(s) = (s_{i+j-2})_{1 \le i,j \le n}.$$
--   In particular its $(1,1)$ entry is $s_0 = n$.
--
--   This identity is what links the Procesi–Schwarz description of the orbit space of the symmetric group to a Hankel matrix, and is the reason the SDP (6.5) involves $H_n(s)$.
--
--   **Formalization Note** The statement is entrywise in 0-based indexing: entry $(i,j)$, $0 \le i,j < n$, of $J$ (built from $\pi_{i+1}, \pi_{j+1}$) equals the power-sum polynomial $s_{i+j}$ (`MvPolynomial.psum`).
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 26, §6.2, "Then the matrix J(z) specializes to the Hankel matrix H_n(s)"; J is (6.1), p. 24

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

namespace SymPolyOpt.PowerSumLB

/-- For the fundamental invariants `π_j = (1/j) s_j` of the symmetric group, the matrix
`J = (⟨dπ_i, dπ_j⟩)` of (6.1) is the Hankel matrix of power sums: in 0-based indexing its
`(i, j)` entry is `s_{i+j}` (the page's `(s_{i+j−2})_{1≤i,j≤n}`). -/
theorem J_eq_hankel (n : ℕ) :
    ∀ i j : Fin n, Jmat n i j = MvPolynomial.psum (Fin n) ℝ ((i : ℕ) + (j : ℕ)) := by sorry

end SymPolyOpt.PowerSumLB
