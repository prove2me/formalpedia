-- Prove2me | Theorems.Thm_TechFinConstr_Selection_corollary_2
-- name    : TechFinConstr.Selection.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:29.455822+00:00
-- url     : https://prove2.me/theorems/251c0cd0-8f81-4a31-8535-e99c1421ed3e
-- title:
--   Corollary 2, p. 13 — ∑_{j≤ῑ(p)} s̄ʲ = min{x, x_ῑ(p)} bounds every optimal contract, with equality iff c = π
-- statement:
--   In Starmans' model, let $p\in\mathscr P$, let $\bar\iota(p)$ be the highest state with $p_i>q_i$, and let $0\le c\le\pi$. Then
--
--   1. the informative tranches sum to a debt payoff: $\sum_{j=1}^{\bar\iota(p)}\bar s^j_i=\min\{x_i,x_{\bar\iota(p)}\}$ for all $i\in\Omega$;
--   2. problem (1) has an optimal contract;
--   3. every optimal contract $s$ satisfies
--   $$s_i\le\min\{x_i,x_{\bar\iota(p)}\}\qquad\text{for all } i\in\Omega,$$
--   and equality holds for all $i\in\Omega$ if and only if $c=\pi$.
--
--   The corollary says that optimal contracts use only the informative tranches, and use all of them in full exactly when the disutility of effort reaches its largest admissible value $\pi$.
--
--   **Formalization Note.** The page states the bound for "an optimal contract from Proposition 1"; the Lean statement asserts it for every optimal contract of problem (1). This is the stronger reading; it holds because weight on a tranche with $\Phi_j(p)=0$ raises the entrepreneur's expected payment without relaxing the incentive constraint (proof of Proposition 1, pp. 34–38). The existence clause excludes a vacuous reading.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 13, Corollary 2 (proof p. 41, Appendix A.7)

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

open Finset

theorem corollary_2 {n : ℕ} (E : Economy n) (hE : E.Standing) (p : Fin (n + 1) → ℝ) (hp : InP E p)
    (c : ℝ) (hc0 : 0 ≤ c) (hcπ : c ≤ E.piE) :
    (∀ i : Fin (n + 1),
      ∑ j ∈ univ.filter (fun j : Fin n => j.succ ≤ iotaBar E p), tranche E j i =
        min (E.x i) (E.x (iotaBar E p))) ∧
    (∃ s, IsOptimalContract E p c s) ∧
    ∀ s, IsOptimalContract E p c s →
      (∀ i, s i ≤ min (E.x i) (E.x (iotaBar E p))) ∧
      ((∀ i, s i = min (E.x i) (E.x (iotaBar E p))) ↔ c = E.piE) := by sorry

end TechFinConstr.Selection
