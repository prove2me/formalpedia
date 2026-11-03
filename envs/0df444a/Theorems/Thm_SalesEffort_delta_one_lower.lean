-- Prove2me | Theorems.Thm_SalesEffort_delta_one_lower
-- name    : SalesEffort.delta_one_lower
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:36.478775+00:00
-- url     : https://prove2.me/theorems/1f22879a-9c19-43b8-9b26-24b60fb155ca
-- title:
--   Online Appendix p.4 — $\Delta_t(1)\ge p+(b-p)\exp(-L_t(1))$
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, let $\lambda^*(t,n)$ be the maximizing rate at $\Delta_t(n)$, and $L_t(1)=\int_0^t\lambda^*(s,1)\,ds$. For every $t\ge0$,
--   $$\Delta_t(1)\ge p+(b-p)\exp(-L_t(1)).$$
--
--   For $b>p$ this is the base case $n=1$ of the "stronger statement" (with $F^{(0)}\equiv b-p>0$): one sale from the target, the marginal value of that sale stays strictly above $p$.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: λ∗(t,n), the unique maximizer of λ∆_t(n) − c(λ) over [λ̲, λ̄] → any function lam with lam t n such a maximizer for every t ≥ 0 and n ≥ 0; reason: the maximizer is unique, so lam is λ∗(t,n) on t ≥ 0; at n = 0 it is λ∗, the paper's λ∗(t,0) = λ∗ (OA p.4)
--   - generalization: derived in the case b > p → stated for every b, p ≥ 0; reason: the derivation uses only that λ∗ maximizes λp − c(λ); the case b > p is a specialization
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Online Appendix p.4 (PDF 38), proof of Theorem 1(ii)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **The lower bound on `∆_t(1)`**, Du, Hu & Wu, SSRN 3506499, Online Appendix p.4 (proof of
Theorem 1(ii)): "∆t(1) = J∗_t(0) − J∗_t(1) ≥ p + (b − p)exp(−Lt(1))", where
`L_t(1) = ∫₀ᵗ λ∗(s,1) ds`.

**Formalization Note.** Stated for every `b, p ≥ 0` (the paper derives it inside the case `b > p`,
but the derivation uses only that `λ∗` maximizes `λp − c(λ)`). `lam` is any profit-maximizing rate
function of `J`; `cumRate lam t 1` is `L_t(1)`. -/
theorem delta_one_lower (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (lam : ℝ → ℕ → ℝ) (hlam : IsRateFn M J lam) (t : ℝ) (ht : 0 ≤ t) :
    M.p + (M.b - M.p) * Real.exp (-cumRate lam t 1) ≤ marginal M J t 1 := by sorry

end SalesEffort
