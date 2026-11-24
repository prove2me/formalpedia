-- Prove2me | Theorems.Thm_VpVnp_no_poly_size_over_real
-- name    : VpVnp.no_poly_size_over_real
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:37:48.268085+00:00
-- url     : https://prove2.me/theorems/cc3b9330-44f4-43e1-aef0-49ec25fd45b3
-- title:
--   Theorem L.2 — no polynomial-size circuits for the permanent over $\mathbb R$
-- statement:
--   The qualitative form of the lower bound over the real numbers: the permanent has no circuits of polynomial size.
--
--   For every integer $C \geq 0$ there is a threshold $m_0$ such that for all $m \geq m_0$, no arithmetic circuit over $\mathbb R$ with at most $m^C$ gates computes the permanent
--   $$\mathrm{PERM}_m = \sum_{\sigma \in S_m} \prod_{i} x_{\sigma(i),\,i}$$
--   of the generic $m \times m$ matrix. Here a circuit is a list of polynomials, each a variable, a real constant, or the sum or product of two earlier entries, and **every** entry counts as a gate, so the size bound $m^C$ includes the variables and constants the circuit starts from. The threshold $m_0$ may depend on $C$.
--
--   This is the weakest of the mission's targets and the first rung of its ladder: it asserts only the shape of the separation over one field, without any quantitative rate. It follows from the quantitative bound of Theorem L.1, since $m^{\,c(\log_2 m)^{1/3}}$ exceeds $m^C$ for large $m$.
--
--   **Formalization Note.** The exponent $C$ is a natural number, following the source's Appendix Q convention that the constants $C$, $a$, $\alpha$ are naturals. The statement is refuted-circuit form: for every gate count $s$ with $s \leq m^C$, $\mathrm{PERM}_m$ has no circuit of size $s$. The base field is fixed to $\mathbb R$.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Appendix L, Theorem L.2, p. 59 (Lean name thm_simple, Table 3, p. 67)

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Polynomials

open MvPolynomial

namespace VpVnp

theorem no_poly_size_over_real :
    ∀ C : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ, s ≤ m ^ C → ¬ Computes (perm ℝ m) s := by sorry

end VpVnp
