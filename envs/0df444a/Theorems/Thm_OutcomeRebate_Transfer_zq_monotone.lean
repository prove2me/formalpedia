-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_zq_monotone
-- name    : OutcomeRebate.Transfer.zq_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:22.276978+00:00
-- url     : https://prove2.me/theorems/7dce6142-f375-4ed0-8339-5c4596ff5c9d
-- title:
--   Proof of Proposition 1, p. 51 (PDF 52) — zq decreases from (0, q0) onto (1, ∞) and zq ≤ 1 on [q0, 1]
-- statement:
--   Let $0 < \alpha < 1$ and $\lambda \ge 1$, and consider $q \mapsto z(q)\,q$ with $z(q) = 1 + (\lambda(1-q)/q)^{1/\alpha}$.
--
--   1. $zq$ is strictly decreasing on $(0, q_0]$.
--   2. It maps $(0, q_0)$ onto $(1, \infty)$.
--   3. $zq \le 1$ for every $q \in [q_0, 1]$.
--   4. Consequently, for every $\kappa > 1$ and every $q_1 \in (0,1)$ with $z(q_1)q_1 = \kappa$, and every $q \in (0,1)$,
--   $$\kappa \le z(q)\,q \iff q \le q_1.$$
--   In particular the solution of $zq = \kappa$ in $(0,1)$ is unique.
--
--   With $\kappa = 2/\beta$, $1/\beta$ and $2/(1+\beta)$, all larger than $1$ since $\beta \le 1/2$, this yields the thresholds $q_1$, $\bar q_1$ and $q_2$ of Proposition 1 and Theorem 1.
--
--   **Formalization Note** The page's interval $[0, q_0)$ starts at $q = 0$, where $z$ is infinite. In Lean $z(0)$ is the junk value $1$, so the statement uses $(0, q_0]$ and $(0, q_0)$.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 51 (PDF 52), proof of Proposition 1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- `zq` as a function of `q` (proof of Proposition 1, p. 51): it is strictly decreasing on
`(0, q₀]` and maps `(0, q₀)` onto `(1, ∞)`; for `q ∈ [q₀, 1]`, `zq ≤ 1`. Consequently, for every
`κ > 1`, a solution `q₁ ∈ (0, 1)` of `zq = κ` satisfies `κ ≤ zq ↔ q ≤ q₁` for every `q ∈ (0, 1)`
(so the solution is unique). -/
theorem zq_monotone (α lam : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) :
    StrictAntiOn (fun q => zOf α lam q * q) (Set.Ioc 0 (q0 α lam)) ∧
      (fun q => zOf α lam q * q) '' Set.Ioo 0 (q0 α lam) = Set.Ioi 1 ∧
      (∀ q ∈ Set.Icc (q0 α lam) 1, zOf α lam q * q ≤ 1) ∧
      (∀ κ q1 : ℝ, 1 < κ → 0 < q1 → q1 < 1 → zOf α lam q1 * q1 = κ →
        ∀ q : ℝ, 0 < q → q < 1 → (κ ≤ zOf α lam q * q ↔ q ≤ q1)) := by sorry

end OutcomeRebate.Transfer
