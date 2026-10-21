-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_constraint_set_lnat_convex
-- name    : PerishablePricing.Backlog.constraint_set_lnat_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:17.357652+00:00
-- url     : https://prove2.me/theorems/2a96c8a8-9414-4a9f-8c05-e1f59662b256
-- title:
--   p. 291 — the set {(s₁, d, a) : a ≥ s₁ ∨ dₜ} is L♮-convex
-- statement:
--   Fix a noise value $\varepsilon$, so that the realized demand is $d_t = d + \varepsilon$. In the coordinates $(s_1, \dots, s_{l-1}, s_l, d, a)$ of $\phi_t$, with $l \ge 2$, the set
--
--   $$\{(s_1, \dots, s_l, d, a) : a \ge s_1 \vee d_t\} = \{(s_1, \dots, s_l, d, a) : a \ge s_1,\ a \ge d + \varepsilon\}$$
--
--   is L♮-convex.
--
--   Together with the removal of the upper bound $a \le s_{l-k} \vee d_t$ by (9), this is what allows Lemma 2 to be applied to the depletion problem (5).
--
--   **Formalization Note** Real case only. The coordinates other than $s_1$, $d$, $a$ are unconstrained, which is the page's three-coordinate set lifted to $\mathbb{R}^{l+2}$. Coordinates are 0-based in `Fin (L+3)` with $L = l - 1$: $s_1$ is coordinate $0$, $d$ is $L + 1$ and $a$ is $L + 2$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §4, proof of Theorem 1, p. 291 (PDF p. 9), "It is easy to check that the set {(s_1, d, a): a ≥ s_1 ∨ d_t} ... is L♮-convex"

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog

/-- p. 291, proof of Theorem 1: for a fixed noise value `ε` (so `d_t = d + ε`), the set
`{(s_1, d, a) : a ≥ s_1 ∨ d_t} = {(s_1, d, a) : a ≥ s_1, a ≥ d_t}` is L♮-convex. It is stated in
the coordinates `w = (s_1, …, s_{l−1}, s_l, d, a) : Fin (L+3) → ℝ` of `φ_t`, with `L = l − 1 ≥ 1`,
so `s_1 = w 0`, `d = w (L+1)`, `a = w (L+2)`, and the other coordinates are free. -/
theorem constraint_set_lnat_convex (L : ℕ) (hL : 1 ≤ L) (ε : ℝ) :
    LNatConvexSet {w : Fin (L + 3) → ℝ |
      w ⟨0, by omega⟩ ≤ w ⟨L + 2, by omega⟩ ∧
        w ⟨L + 1, by omega⟩ + ε ≤ w ⟨L + 2, by omega⟩} := by sorry

end PerishablePricing.Backlog
