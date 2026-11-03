-- Prove2me | Theorems.Thm_SalesEffort_delta_one_upper_of_b_le_p
-- name    : SalesEffort.delta_one_upper_of_b_le_p
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:43.857473+00:00
-- url     : https://prove2.me/theorems/416b9274-5a23-4f1d-8b19-b47f2b99093a
-- title:
--   Online Appendix p.4 — $\Delta_t(1)\le p-(p-b)e^{-\lambda^*t}\le p$ when $b\le p$
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, and assume $b\le p$. For every $t\ge0$,
--   $$\Delta_t(1)\le p-(p-b)e^{-\lambda^*t}\le p.$$
--
--   The bound starts the induction that proves Theorem 1(iii): it shows that $\Delta_t(1)$ never exceeds $\Delta_t(0)=p$, hence (by Inequality (OA.1)) is nondecreasing in $t$.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: ∆_t(1) ≤ e^{−λ∗t}[∆_0(0) + ∫_0^t λ∗e^{λ∗s}∆_s(0)ds] = e^{−λ∗t}[b + p∫_0^t λ∗e^{λ∗s}ds] = p − (p − b)e^{−λ∗t} ≤ p → the closed-form bound and its comparison with p; reason: the intermediate expressions are derivation steps; their printed initial value ∆_0(0) is a slip for ∆_0(1) = b, as the next expression shows
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Online Appendix p.4 (PDF 38), proof of Theorem 1(iii)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **The upper bound on `∆_t(1)` when `b ≤ p`**, Du, Hu & Wu, SSRN 3506499, Online Appendix p.4
(proof of Theorem 1(iii)): `∆t(1) ≤ … = p − (p − b)e^{−λ∗t} ≤ p`.

**Formalization Note.** The display's printed initial value "∆0(0)" is `∆_0(1) = b` (the next
expression in the same display reads `b`); the bound itself is stated. `t` ranges over `[0, ∞)`. -/
theorem delta_one_upper_of_b_le_p (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (hbp : M.b ≤ M.p) (t : ℝ) (ht : 0 ≤ t) :
    marginal M J t 1 ≤ M.p - (M.p - M.b) * Real.exp (-(M.lstar * t)) ∧
      M.p - (M.p - M.b) * Real.exp (-(M.lstar * t)) ≤ M.p := by sorry

end SalesEffort
