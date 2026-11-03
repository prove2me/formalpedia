-- Prove2me | Theorems.Thm_SalesEffort_inequality_OA_1
-- name    : SalesEffort.inequality_OA_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:41.353504+00:00
-- url     : https://prove2.me/theorems/3292fd79-aa74-4687-a6de-24c5bb7bc35a
-- title:
--   Inequality (OA.1), Online Appendix p.2 — the sandwich bound on $\partial\Delta_t(n)/\partial t$
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, let $\Delta_t(n)=J_t(n-1)-J_t(n)$ with $\Delta_t(0)=p$, and let $\lambda^*(t,n)$ be the maximizing rate at $\Delta_t(n)$ (so $\lambda^*(t,0)=\lambda^*$). For every $n\ge1$ and $t\ge0$, $t\mapsto\Delta_t(n)$ is differentiable at $t$ (one-sided at $0$) and
--   $$\lambda^*(t,n)\big[\Delta_t(n-1)-\Delta_t(n)\big]\le\frac{\partial\Delta_t(n)}{\partial t}\le\lambda^*(t,n-1)\big[\Delta_t(n-1)-\Delta_t(n)\big].$$
--
--   The inequality says that $\Delta_t(n)$ moves toward $\Delta_t(n-1)$, at a speed between the two optimal rates. It drives every step of the proof of Theorem 1.
--
--   **Formalization Note** The statement is indexed by $n+1$; the derivative is taken within $[0,\infty)$ and its existence is part of the conclusion.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: λ∗(t,n), the unique maximizer of λ∆_t(n) − c(λ) over [λ̲, λ̄] → any function lam with lam t n such a maximizer for every t ≥ 0 and n ≥ 0; reason: the maximizer is unique, so lam is λ∗(t,n) on t ≥ 0; at n = 0 it is λ∗, the paper's λ∗(t,0) = λ∗ (OA p.4)
--   - encoding: ∆_t(n) := J∗_t(n−1) − J∗_t(n), and J∗_t(−1) = J∗(0) + p (OA p.2) → marginal M J t n, equal to p at n = 0; reason: the paper's own convention ∆_t(0) = p
--   - encoding: ∂∆_t(n)/∂t for n ≥ 1 → a derivative of s ↦ ∆_s(n+1) within [0, ∞) at t ≥ 0, whose existence is concluded; reason: time to go is t ≥ 0; ℕ index shifted to avoid truncated subtraction
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Inequality (OA.1), Online Appendix p.2 (PDF 36)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **Inequality (OA.1)**, Du, Hu & Wu, SSRN 3506499, Online Appendix p.2: for `n ≥ 1`,
`λ∗(t,n)[∆t(n − 1) − ∆t(n)] ≤ ∂∆t(n)/∂t ≤ λ∗(t,n − 1)[∆t(n − 1) − ∆t(n)]`,
with `∆_t(0) = p` and `λ∗(t,0) = λ∗`.

**Formalization Note.** Indexed by `n + 1` (so `n + 1 ≥ 1`). The derivative is the derivative of
`s ↦ ∆_s(n+1)` within `[0, ∞)` at `t ≥ 0`; its existence is part of the conclusion. `lam` is any
profit-maximizing rate function of `J` (`IsRateFn`), the paper's `λ∗(t,n)`. -/
theorem inequality_OA_1 (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (lam : ℝ → ℕ → ℝ) (hlam : IsRateFn M J lam) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ d : ℝ, HasDerivWithinAt (fun s => marginal M J s (n + 1)) d (Ici 0) t ∧
      lam t (n + 1) * (marginal M J t n - marginal M J t (n + 1)) ≤ d ∧
      d ≤ lam t n * (marginal M J t n - marginal M J t (n + 1)) := by sorry

end SalesEffort
