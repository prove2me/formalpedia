-- Prove2me | Theorems.Thm_SalesEffort_cumRate_diff_bounded_below
-- name    : SalesEffort.cumRate_diff_bounded_below
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:00.668057+00:00
-- url     : https://prove2.me/theorems/5993f80b-10a7-468a-8f21-0506bc9b45cc
-- title:
--   Online Appendix pp.4–5 — $L_t(n)-L_t(n-1)$ is bounded from below
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, let $\lambda^*(t,n)$ be the maximizing rate at $\Delta_t(n)$, $L_t(n)=\int_0^t\lambda^*(s,n)\,ds$, and assume $b>p$. Let $n\ge2$ and $\eta\ge0$. If $\Delta_t(n-1)$ is nonincreasing in $t$ on $[\eta,\infty)$, then there is a constant $\mathscr C$ such that
--   $$L_t(n)-L_t(n-1)\ge\mathscr C\qquad\text{for every }t\ge\eta.$$
--
--   This is the step of the induction where the strong convexity of $c$ enters: it keeps the polynomial factor of the "stronger statement" from being absorbed by the exponential.
--
--   **Formalization Note** The statement is indexed by $n+2$.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: λ∗(t,n), the unique maximizer of λ∆_t(n) − c(λ) over [λ̲, λ̄] → any function lam with lam t n such a maximizer for every t ≥ 0 and n ≥ 0; reason: the maximizer is unique, so lam is λ∗(t,n) on t ≥ 0; at n = 0 it is λ∗, the paper's λ∗(t,0) = λ∗ (OA p.4)
--   - reading: ∆_t(n − 1) decreases in t when t ≥ η → AntitoneOn on [η, ∞); reason: monotonicity in the paper is weak (OA p.4)
--   - encoding: L_t(n) − L_t(n−1) ≥ 𝒞, 𝒞 a constant independent of t → ∃ C, ∀ t ≥ η, C ≤ L_t(n+2) − L_t(n+1), with L as an interval integral of lam; reason: the range t ≥ η is the one on which the proof establishes the bound
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Online Appendix pp.4–5 (PDF 38–39), proof of Theorem 1(ii)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **`L_t(n) − L_t(n−1)` is bounded from below**, Du, Hu & Wu, SSRN 3506499, Online Appendix
pp.4–5 (proof of Theorem 1(ii), `b > p`): if `∆_t(n − 1)` decreases in `t` for `t ≥ η`, then
"Lt(n) − Lt(n−1) ≥ 𝒞", with `𝒞` a constant independent of `t`.

**Formalization Note.** Indexed by `n + 2` (so `n + 2 ≥ 2`). "Decreases in `t` for `t ≥ η`" is weak
monotonicity on `[η, ∞)`, with `η ≥ 0` as printed. The bound is claimed for `t ≥ η`, the range on
which the proof establishes it. -/
theorem cumRate_diff_bounded_below (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (lam : ℝ → ℕ → ℝ) (hlam : IsRateFn M J lam) (hbp : M.p < M.b) (n : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hdec : AntitoneOn (fun t => marginal M J t (n + 1)) (Ici η)) :
    ∃ C : ℝ, ∀ t : ℝ, η ≤ t → C ≤ cumRate lam t (n + 2) - cumRate lam t (n + 1) := by sorry

end SalesEffort
