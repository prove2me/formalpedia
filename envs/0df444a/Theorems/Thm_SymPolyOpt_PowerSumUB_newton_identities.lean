-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumUB_newton_identities
-- name    : SymPolyOpt.PowerSumUB.newton_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:50.628893+00:00
-- url     : https://prove2.me/theorems/25bff274-9101-4e13-b74d-64bcce01f8a7
-- title:
--   §6.2, p. 27 — Newton's identities relating the Newton sums and the coefficients of a monic polynomial
-- statement:
--   Let $p = X^m + \sum_{j=0}^{m-1} p_j X^j$ be a monic real polynomial of degree $m$, and let $s_k = \sum_z z^k$ be its Newton sums, the sum over the complex roots of $p$ with multiplicity. Then
--   $$
--   \begin{aligned}
--   s_k + p_{m-1} s_{k-1} + \cdots + p_0 s_{k-m} &= 0 && (k \ge m),\\
--   s_k + p_{m-1} s_{k-1} + \cdots + p_{m-k+1} s_1 &= -k\, p_{m-k} && (1 \le k < m).
--   \end{aligned}
--   $$
--
--   These identities make the Newton sums polynomials in the coefficients and, conversely, determine $p_{m-1}, \dots, p_1$ from $s_1, \dots, s_{m-1}$. They underlie the reduction of the SDP (6.6) to the one-variable SDP (6.7).
--
--   **Formalization Note** The first family is written $s_k + \sum_{i=0}^{m-1} p_i\, s_{k-m+i} = 0$ for $k \ge m$, and the second $s_k + \sum_{i=1}^{k-1} p_{m-i}\, s_{k-i} = -k\, p_{m-k}$ for $1 \le k < m$; with these ranges no natural-number subtraction truncates.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 27, §6.2, display after "related by Newton's identities"

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumUB_Setting

namespace SymPolyOpt.PowerSumUB

open Polynomial

theorem newton_identities (m : ℕ) (p : ℝ[X]) (hp : p.Monic) (hdeg : p.natDegree = m) :
    (∀ k : ℕ, m ≤ k →
      newtonSum p k + ∑ i ∈ Finset.range m, p.coeff i * newtonSum p (k - m + i) = 0) ∧
    (∀ k : ℕ, 1 ≤ k → k < m →
      newtonSum p k + ∑ i ∈ Finset.Ico 1 k, p.coeff (m - i) * newtonSum p (k - i) =
        -(k : ℝ) * p.coeff (m - k)) := by sorry

end SymPolyOpt.PowerSumUB
