-- Prove2me | Theorems.Thm_SalesEffort_stronger_statement
-- name    : SalesEffort.stronger_statement
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:37.632922+00:00
-- url     : https://prove2.me/theorems/2c2d5a49-1d03-42ed-839a-a0739fef7624
-- title:
--   Online Appendix p.4 — the stronger statement $\Delta_t(n)\ge p+\exp(-L_t(n))F^{(n-1)}(t)$ for large $t$ when $b>p$
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, let $\lambda^*(t,n)$ be the maximizing rate at $\Delta_t(n)$, $L_t(n)=\int_0^t\lambda^*(s,n)\,ds$, and assume $b>p$. For every $n\ge1$ there are $\eta_n\ge0$ and a real polynomial
--   $$F^{(n-1)}(t)=\theta^{(n-1)}t^{n-1}+\theta^{(n-2)}t^{n-2}+\cdots+\theta^{(0)},\qquad\theta^{(n-1)}>0,$$
--   such that
--   $$\Delta_t(n)\ge p+\exp(-L_t(n))\,F^{(n-1)}(t)\qquad\text{for every }t\ge\eta_n.$$
--
--   Since $F^{(n-1)}(t)>0$ for large $t$, $\Delta_t(n)>p$ eventually: the marginal value approaches its limit $p$ from above, which is what forces it to first increase and then decrease.
--
--   **Formalization Note** The statement is indexed by $n+1$: $F$ has degree exactly $n$ and positive leading coefficient.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: λ∗(t,n), the unique maximizer of λ∆_t(n) − c(λ) over [λ̲, λ̄] → any function lam with lam t n such a maximizer for every t ≥ 0 and n ≥ 0; reason: the maximizer is unique, so lam is λ∗(t,n) on t ≥ 0; at n = 0 it is λ∗, the paper's λ∗(t,0) = λ∗ (OA p.4)
--   - encoding: an η_n with F^{(n−1)} = θ^{(n−1)}t^{n−1} + ⋯ + θ^{(0)}, θ^{(n−1)} > 0 → η ≥ 0 and F : Polynomial ℝ with natDegree n and leadingCoeff > 0, at index n + 1; reason: t ranges over the time to go [0, ∞); same polynomials
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Online Appendix p.4 (PDF 38), proof of Theorem 1(ii)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **The "stronger statement"**, Du, Hu & Wu, SSRN 3506499, Online Appendix p.4 (proof of
Theorem 1(ii)): when `b > p`, for every `n ≥ 1` "there exists an ηn such that for any t ≥ ηn,
∆t(n) ≥ p + exp(−Lt(n))F^{(n−1)}(t), where F^{(n−1)}(t) = θ^{(n−1)}t^{n−1} + ⋯ + θ^{(0)} with
θ^{(n−1)} > 0".

**Formalization Note.** Indexed by `n + 1` (so `n + 1 ≥ 1`); `F^{(n)}` is a real polynomial of
degree exactly `n` with positive leading coefficient, evaluated at `t`. `η` is taken in `[0, ∞)`,
the domain of the time to go. `cumRate lam t (n+1)` is `L_t(n+1) = ∫₀ᵗ λ∗(s,n+1) ds`. -/
theorem stronger_statement (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (lam : ℝ → ℕ → ℝ) (hlam : IsRateFn M J lam) (hbp : M.p < M.b) (n : ℕ) :
    ∃ η : ℝ, 0 ≤ η ∧ ∃ F : Polynomial ℝ, F.natDegree = n ∧ 0 < F.leadingCoeff ∧
      ∀ t : ℝ, η ≤ t →
        M.p + Real.exp (-cumRate lam t (n + 1)) * F.eval t ≤ marginal M J t (n + 1) := by sorry

end SalesEffort
