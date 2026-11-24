-- Prove2me | Theorems.Thm_VpVnp_main_theorem_approx
-- name    : VpVnp.main_theorem_approx
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T23:41:44.098832+00:00
-- url     : https://prove2.me/theorems/5141ffd7-04fe-419f-ac75-cb51e1900a0a
-- title:
--   Theorem 1.4 (first assertion) — the lower bound for approximating circuits over every field
-- statement:
--   The border form of the mission's goal: the same superpolynomial bound for circuits that only **approximate** the target.
--
--   There is an absolute constant $c > 0$ such that for every $p$, zero or prime, there is a threshold $m_0$ with the following property. Over every field $F$ of characteristic $p$ and for every $m \geq m_0$:
--
--   1. every circuit over the Laurent series field $F((\varepsilon))$ that approximates the Hamiltonian cycle polynomial $\mathrm{HC}_m$ has more than $m^{\,c\,(\log_2 m)^{1/3}}$ gates; and
--   2. if $p \neq 2$, every circuit over $F((\varepsilon))$ that approximates the permanent $\mathrm{PERM}_m$ has more than $m^{\,c\,(\log_2 m)^{1/3}}$ gates.
--
--   Here a circuit **approximates** a polynomial $f$ over $F$ if it computes $f + \varepsilon g$ where every coefficient of $g$ is a power series in $\varepsilon$; the gate count is the same as for exact computation, with variables and constants of $F((\varepsilon))$ counted as gates. Over $\mathbb R$ this says that $f$ is not even a coefficientwise limit of polynomials with small circuits, although constants such as $1/\varepsilon$ may diverge in the limit. This is the statement that the geometric complexity theory programme aims at over $\mathbb C$ in the language of orbit closures.
--
--   The assertion is strictly stronger than the goal, since a circuit computing $f$ also approximates it. Together with the membership of $(\mathrm{HC}_m)$ in VNP it yields $\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}$ over every field, the second assertion of the source's Theorem 1.4.
--
--   **Formalization Note.** This is the first assertion of the source's Theorem N.5, which its Appendix Q identifies with `MainTheoremApprox`. Approximation is expressed coefficientwise: for every monomial and every integer $i \leq 0$, the coefficient of $\varepsilon^i$ equals that of $f$ for $i = 0$ and vanishes for $i < 0$. The characteristic ranges over all naturals, with `CharP F p` forcing $p = 0$ or prime; the field is universe-polymorphic.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Theorem 1.4, p. 2, stated and proved as Appendix N, Theorem N.5, p. 64, first assertion (Lean name thm_approx, Table 3, p. 67); Lean vp-vnp/Statement.lean, def Statement.MainTheoremApprox

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Polynomials
import Definitions.Def_VpVnp_Beyond
import Definitions.Def_VpVnp_Approximates

open MvPolynomial

universe u

namespace VpVnp

theorem main_theorem_approx :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (hc F m) s → Beyond c m s) ∧ (p ≠ 2 → Approximates (perm F m) s → Beyond c m s) := by sorry

end VpVnp
