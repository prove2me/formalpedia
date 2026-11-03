-- Prove2me | Theorems.Thm_SalesEffort_lemma_A1_iii
-- name    : SalesEffort.lemma_A1_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:52.458913+00:00
-- url     : https://prove2.me/theorems/efc494d7-728a-4800-98c9-85772471b3b6
-- title:
--   Lemma A1(iii), Online Appendix p.2 — $\lambda^*(t,n)\to\lambda^*$ as $t\to\infty$
-- statement:
--   Let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, and let $\lambda^*(t,n)$ be the maximizing rate at $\Delta_t(n)$. For every $n\ge0$,
--   $$\lim_{t\to\infty}\lambda^*(t,n)=\lambda^*.$$
--
--   With much time left, the target is reached almost surely and the seller behaves as if every sale earned $p$.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: λ∗(t,n), the unique maximizer of λ∆_t(n) − c(λ) over [λ̲, λ̄] → any function lam with lam t n such a maximizer for every t ≥ 0 and n ≥ 0; reason: the maximizer is unique, so lam is λ∗(t,n) on t ≥ 0; at n = 0 it is λ∗, the paper's λ∗(t,0) = λ∗ (OA p.4)
--   - encoding: ∆_t(n) := J∗_t(n−1) − J∗_t(n), and J∗_t(−1) = J∗(0) + p (OA p.2) → marginal M J t n, equal to p at n = 0; reason: the paper's own convention ∆_t(0) = p
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Lemma A1(iii), Online Appendix p.2 (PDF 36)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **Lemma A1(iii)**, Du, Hu & Wu, SSRN 3506499, Online Appendix p.2: "∀n ≥ 0,
lim_{t→∞} λ∗(t,n) = λ∗".

**Formalization Note.** `lam` is any profit-maximizing rate function of the HJB solution `J`
(`IsRateFn`), the paper's `λ∗(t,n)`; `λ∗` is `M.lstar`. -/
theorem lemma_A1_iii (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (lam : ℝ → ℕ → ℝ) (hlam : IsRateFn M J lam) (n : ℕ) :
    Tendsto (fun t => lam t n) atTop (𝓝 M.lstar) := by sorry

end SalesEffort
