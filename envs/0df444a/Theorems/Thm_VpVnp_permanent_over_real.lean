-- Prove2me | Theorems.Thm_VpVnp_permanent_over_real
-- name    : VpVnp.permanent_over_real
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:38:25.306432+00:00
-- url     : https://prove2.me/theorems/b658fd02-887b-4d79-b472-b08c8de331d0
-- title:
--   Theorem L.1 — quasipolynomial circuit lower bound for the permanent over $\mathbb R$
-- statement:
--   The main theorem of the source's main text: a superpolynomial lower bound for general arithmetic circuits computing the real permanent.
--
--   There are a constant $c > 0$ and a threshold $m_0$ such that for every $m \geq m_0$ and every $s \in \mathbb N$, if the permanent
--   $$\mathrm{PERM}_m = \sum_{\sigma \in S_m} \prod_{i} x_{\sigma(i),\,i}$$
--   of the generic $m \times m$ matrix has an arithmetic circuit over $\mathbb R$ with at most $s$ gates, then
--   $$m^{\,c\,(\log_2 m)^{1/3}} < s .$$
--
--   Equivalently, every circuit over $\mathbb R$ computing $\mathrm{PERM}_m$ has more than $m^{\,c(\log_2 m)^{1/3}} = 2^{\,c(\log_2 m)^{4/3}}$ gates. The bound is quasipolynomial: it exceeds every fixed polynomial in $m$ for large $m$, while the best known upper bounds are exponential. No restriction is placed on the depth of the circuit, on its constants, or on cancellation; variables and constants count as gates.
--
--   This is the real-number case of the mission's goal (Theorem 1.1), and the statement the source's proof reaches first; the goal extends it to every field and to the Hamiltonian cycle polynomial.
--
--   **Formalization Note.** The constant $c$ is existentially quantified before $m_0$, and the exponent $1/3$ is the source's claim, not asserted to be optimal. The threshold uses real exponentiation and $\log_2$; the strict inequality is between reals, with $s$ cast from $\mathbb N$.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Appendix L, Theorem L.1, p. 59 (Lean names thm_main, thm_main_form, Table 3, p. 67); Lean vp-vnp/Challenge.lean and Solution.lean, theorem permanent_over_real

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Polynomials
import Definitions.Def_VpVnp_Beyond

open MvPolynomial

namespace VpVnp

theorem permanent_over_real : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (perm ℝ m) s → Beyond c m s := by sorry

end VpVnp
