-- Prove2me | Theorems.Thm_RevShareCoord_Single_integrated_optimum
-- name    : RevShareCoord.Single.integrated_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:49.135877+00:00
-- url     : https://prove2.me/theorems/c2a2f895-36b3-4a66-a8e4-9c35ee4c8ac7
-- title:
--   Sec. 2.1, Eq. (1) — the integrated channel's optimal quantity q_I exists, is unique and positive, and solves R′(q_I) = c
-- statement:
--   Consider the single-retailer model: $R$ is strictly concave and differentiable on $[0,\infty)$ with derivative $R'$, the unit cost is $c > 0$, $R'(0) > c$ and $R'(\infty) < c$. The total supply chain profit is $\Pi(q) = R(q) - qc$.
--
--   Then the integrated channel has a unique optimal order quantity $q_I$ on $[0, \infty)$, it is positive, and it satisfies the first-order condition
--
--   $$
--   R'(q_I) = c .
--   $$
--
--   Moreover $q_I$ is the only positive solution of $R'(q) = c$.
--
--   This is the benchmark against which every contract is measured: a contract coordinates the channel when it makes the retailer order $q_I$.
--
--   **Formalization Note.** The paper's sentence reads "Since $R(q)$ is concave and $R'(0) \ge c$"; the weak inequality is a slip, since with $R'(0) = c$ the optimum is $q_I = 0$, which is not positive. The statement uses the standing assumption $R'(0) > c$ of Sec. 1 (p. 5). Optimality is maximization of $\Pi$ over all $q \ge 0$; the converse clause (every positive root of $R'(q) = c$ is $q_I$) makes explicit that Eq. (1) characterizes $q_I$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 6 (PDF p. 7), Section 2.1, Eq. (1); standing assumptions p. 5, Section 1

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.1, Eq. (1), p. 6: the integrated channel has a unique optimal order quantity
`q_I` on `[0, ∞)`; it is positive and satisfies `R'(q_I) = c`, and it is the only positive
solution of `R'(q) = c`. -/
theorem integrated_optimum (M : Model) :
    ∃ qI : ℝ, 0 < qI ∧ M.R' qI = M.c ∧ IsMaxOn M.Pi (Set.Ici 0) qI ∧
      (∀ q : ℝ, 0 ≤ q → IsMaxOn M.Pi (Set.Ici 0) q → q = qI) ∧
      (∀ q : ℝ, 0 < q → M.R' q = M.c → q = qI) := by sorry

end RevShareCoord.Single
