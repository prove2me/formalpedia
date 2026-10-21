-- Prove2me | Theorems.Thm_TechFinConstr_Selection_corollary_3
-- name    : TechFinConstr.Selection.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:20.887669+00:00
-- url     : https://prove2.me/theorems/61ef84a3-4467-49b3-97b8-585eaaf41141
-- title:
--   Corollary 3, p. 16 — E_q[s*(p)] ≤ E_q[min{x, x_ῑ(p)}], with equality iff c = π
-- statement:
--   In Starmans' model, let $p\in\mathscr P$, let $\bar\iota(p)$ be the highest state with $p_i>q_i$, and let $0\le c\le\pi$. Then problem (1) has an optimal contract, and every optimal contract $s$ satisfies
--   $$\mathbb E_q[s]\le\mathbb E_q\bigl[\min\{x,x_{\bar\iota(p)}\}\bigr],$$
--   with equality if and only if $c=\pi$.
--
--   The agency rent is therefore bounded by the expected value, under the shirking distribution, of debt with face value $x_{\bar\iota(p)}$, and reaches this bound exactly at $c=\pi$. The proof of the main comparison (Proposition 6) uses it at $c=\pi$.
--
--   **Formalization Note.** As in Corollary 2, "an optimal contract from Proposition 1" is read as every optimal contract of problem (1) (footnote 7, p. 11), and an existence clause is added.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 16, Corollary 3

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem corollary_3 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p)
    (c : ℝ) (hc0 : 0 ≤ c) (hcπ : c ≤ E.piE) :
    (∃ s, IsOptimalContract E p c s) ∧
    ∀ s, IsOptimalContract E p c s →
      expect E.q s ≤ expect E.q (fun i => min (E.x i) (E.x (iotaBar E p))) ∧
      (expect E.q s = expect E.q (fun i => min (E.x i) (E.x (iotaBar E p))) ↔ c = E.piE) := by sorry

end TechFinConstr.Selection
