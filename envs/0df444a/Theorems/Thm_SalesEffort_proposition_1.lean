-- Prove2me | Theorems.Thm_SalesEffort_proposition_1
-- name    : SalesEffort.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:51.267036+00:00
-- url     : https://prove2.me/theorems/5600b966-7c01-41f6-9d73-9cce412184c6
-- title:
--   Proposition 1, p.11 (well-posedness part; the identification of $J^*$ with the value of (S) is not stated) — the HJB system (2) has exactly one solution on $t\ge0$, and the maximizing rate is unique
-- statement:
--   Let the model satisfy Assumption 1 (with $c$ continuous and $\alpha$-strongly convex on $[\underline\lambda,\bar\lambda]$). Then:
--
--   1. the HJB system
--   $$\frac{\partial J_t(n)}{\partial t}=\max_{\lambda\in[\underline\lambda,\bar\lambda]}\big\{\lambda[J_t(n-1)-J_t(n)]-c(\lambda)\big\},\qquad n\ge1,\ t\ge0,$$
--   with $J_0(n)=0$ for $n\ge1$ and $J_t(0)=b+[\lambda^*p-c(\lambda^*)]t$, has a solution $J$;
--   2. any two solutions agree at every $t\ge0$ and every $n$;
--   3. for every marginal value $\Delta$, the maximizer of $\lambda\Delta-c(\lambda)$ over $[\underline\lambda,\bar\lambda]$ exists and is unique.
--
--   This is the well-posedness of (2) on which Theorem 1 rests: the optimal expected profit $J^*_t(n)$ of the paper is this solution, and $\lambda^*(t,n)$ is the unique maximizer at $\Delta_t(n)$.
--
--   **Formalization Note** $J$ is a function of $(t,n)\in\mathbb R\times\mathbb N$; derivatives are taken within $[0,\infty)$. The identification of the solution with the value of the stochastic control problem (S) is not part of this statement.
--
--   Differences from the source:
--   - encoding: J∗_t(n), the optimal expected profit of (S), is the solution of (2); there exists a unique solution λ∗(t,n) → (2) with its boundary conditions has a solution on t ∈ [0, ∞), solutions agree on t ≥ 0, and the maximizer at every ∆ is unique; reason: the ODE content of Proposition 1, which is all Theorem 1 uses; the identification with the value of (S) needs a controlled point process and is not formalized in this mission
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: ∀t → t ∈ [0, ∞), derivative within [0, ∞) (one-sided at t = 0), maximum attained; reason: t is the time to go
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Proposition 1 and the following paragraph, p.11 (PDF 12)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **Proposition 1** (ODE content), Du, Hu & Wu, *Sales Effort Management under All-or-Nothing
Constraint*, SSRN 3506499, p.11: the HJB system (2), with boundary conditions `J_0(n) = 0` for
`n ≥ 1` and `J_t(0) = b + [λ∗p − c(λ∗)]t`, has a solution on `t ∈ [0, ∞)`; any two solutions agree
on `t ≥ 0`; and for every marginal value `Δ` the maximizer of `λΔ − c(λ)` over `[λ̲, λ̄]` is unique
("There exists a unique solution to Equation (2), which we denote by λ∗(t,n)", p.11).

**Formalization Note.** The identification of the solution with the optimal expected profit of the
stochastic control problem (S) is not formalized; this item is the well-posedness of (2) that
Theorem 1 rests on. -/
theorem proposition_1 (M : Model) :
    (∃ J : ℝ → ℕ → ℝ, IsHJBSolution M J) ∧
    (∀ J₁ J₂ : ℝ → ℕ → ℝ, IsHJBSolution M J₁ → IsHJBSolution M J₂ →
      ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, J₁ t n = J₂ t n) ∧
    (∀ Δ : ℝ, ∃! ℓ : ℝ, IsOptRate M Δ ℓ) := by sorry

end SalesEffort
