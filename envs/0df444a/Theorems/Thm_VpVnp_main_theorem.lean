-- Prove2me | Theorems.Thm_VpVnp_main_theorem
-- name    : VpVnp.main_theorem
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:40:02.661338+00:00
-- url     : https://prove2.me/theorems/eadc71a1-95fa-42ed-9718-dcebe5806d1d
-- title:
--   Theorem 1.1 — superpolynomial circuit lower bounds for $\mathrm{HC}_m$ and $\mathrm{PERM}_m$ over every field
-- statement:
--   The mission's goal, and the source's main theorem: an absolute superpolynomial lower bound for general arithmetic circuits, over every field.
--
--   There is an absolute constant $c > 0$ such that for every $p$, zero or prime, there is a threshold $m_0$ with the following property. Over every field $F$ of characteristic $p$ and for every $m \geq m_0$:
--
--   1. every arithmetic circuit over $F$ computing the Hamiltonian cycle polynomial
--   $$\mathrm{HC}_m = \sum_{\substack{\sigma \in S_m \\ \sigma \text{ a single } m\text{-cycle}}} \prod_{i} x_{i,\,\sigma(i)}$$
--   has more than $m^{\,c\,(\log_2 m)^{1/3}}$ gates; and
--   2. if $p \neq 2$, every arithmetic circuit over $F$ computing the permanent $\mathrm{PERM}_m$ has more than $m^{\,c\,(\log_2 m)^{1/3}}$ gates.
--
--   The constant $c$ is chosen once, before $p$; the threshold $m_0$ may depend on $p$ but not on the field $F$ or on $m$. Circuits are lists of polynomials built from variables and field constants by addition and multiplication of earlier entries, and every entry counts as a gate. No restriction is imposed on depth, on the constants used, or on cancellation. In characteristic two the permanent equals the determinant and has polynomial-size circuits, which is why clause 2 excludes $p = 2$; the Hamiltonian cycle polynomial is VNP-complete over every field, so clause 1 has no exception.
--
--   Since $(\mathrm{HC}_m)$ lies in VNP, this bound separates VP from VNP over every field (Corollary 1.2). It does not settle P vs NP: an arithmetic circuit must be correct on all inputs from the field and its extensions, not only on $0/1$ inputs.
--
--   **Formalization Note.** The characteristic $p$ ranges over all natural numbers; `CharP F p` for a field forces $p = 0$ or $p$ prime, so the other values of $p$ hold vacuously. The statement is universe-polymorphic in the field, matching the source's `MainTheorem.{u}`. The bound `Beyond c m s` is the strict inequality $m^{\,c(\log_2 m)^{1/3}} < s$ with real exponentiation.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Theorem 1.1, p. 2, stated and proved as Appendix M, Theorem M.3, pp. 61-62 (Lean name thm_allfields, Table 3, p. 67); Lean vp-vnp/Statement.lean, def Statement.MainTheorem

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Polynomials
import Definitions.Def_VpVnp_Beyond

open MvPolynomial

universe u

namespace VpVnp

theorem main_theorem :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Computes (hc F m) s → Beyond c m s) ∧ (p ≠ 2 → Computes (perm F m) s → Beyond c m s) := by sorry

end VpVnp
