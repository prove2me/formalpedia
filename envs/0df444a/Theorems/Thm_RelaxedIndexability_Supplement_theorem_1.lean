-- Prove2me | Theorems.Thm_RelaxedIndexability_Supplement_theorem_1
-- name    : RelaxedIndexability.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:04:15.008813+00:00
-- url     : https://prove2.me/theorems/6022809a-6e7c-422a-b1bb-8f691fa5e7b4
-- title:
--   Theorem 1 — the right derivative of $V_{\beta,m}$ in $m$ is the maximal optimal passive time, and an equivalent condition for indexability
-- statement:
--   Consider one arm with $K$ states, a row-stochastic transition matrix $\mathbf P$, a reward vector $B$ and a discount factor $\beta\in(0,1)$. Let $V_{\beta,m}(\omega)$ be the optimal value of the single-armed bandit with subsidy $m$, $V_{\beta,m}(\omega;u)$ the optimal action values (13)–(14), $\Pi^*_{sa}(m)$ the set of optimal single-arm policies from $\omega$ and $C(m)$ the decision boundary (20).
--
--   1. For every belief $\omega$ and every $m_0$, the passive time
--   $$
--   D_{\beta,m_0}(\omega)=\max_{\pi\in\Pi^*_{sa}(m_0)}\mathbb E_\pi\Big[\sum_{t=1}^\infty\beta^{t-1}\mathbb 1(u(t)=0)\ \Big|\ \omega(1)=\omega\Big]
--   $$
--   is attained, the right derivative of $m\mapsto V_{\beta,m}(\omega)$ at $m_0$ exists, and
--   $$
--   \frac{dV_{\beta,m}(\omega)}{(dm)^+}\bigg|_{m=m_0}=D_{\beta,m_0}(\omega).
--   $$
--   2. The arm is indexable (Definition 1) if and only if for every belief $\omega$ and every $m_\omega$ with $\omega\in C(m_\omega)$ the right derivatives of the two action values at $m_\omega$ exist and satisfy
--   $$
--   \frac{dV_{\beta,m}(\omega;u=0)}{(dm)^+}\bigg|_{m=m_\omega}\ \ge\ \frac{dV_{\beta,m}(\omega;u=1)}{(dm)^+}\bigg|_{m=m_\omega},
--   $$
--   and, when equality holds, there is $\Delta m(\omega)>0$ such that $V_{\beta,m}(\omega;u=0)\ge V_{\beta,m}(\omega;u=1)$ for all $m\in(m_\omega,m_\omega+\Delta m(\omega))$.
--
--   The first part identifies the slope of the optimal value with a passive time; the second reduces indexability to a local condition on the decision boundary, which Theorem 2 verifies for $\beta\le1/2$.
--
--   **Formalization Note** A right derivative is `HasDerivWithinAt` on the interval $(m_0,\infty)$, which asserts that it exists. The maximum is stated as a greatest element of the set of optimal passive times.
--
--   Differences from the source:
--   - reading: ∀ m ∈ (m_ω + ∆m(ω)) → ∀ m ∈ (m_ω, m_ω + ∆m(ω)); reason: the printed interval lost its left end; the proof negates (25) as "for any ε₁ > 0 there exists m₂ (m_ω < m₂ < m_ω + ε₁)" in (EC.29), p.ec8
--   - generalization: P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: the theorem does not use them; every row-stochastic P and every B include the source's case
--   - generalization: an arm has a positive finite number K of states → the referenced Arm permits K = 0; reason: the K = 0 simplex and decision boundary are empty, so both theorem clauses reduce to true statements, while every source arm has K > 0
--   - encoding: single-arm policies → deterministic history-dependent policies; reason: they include the time-dependent belief policies of p.ec1, and the optimal value and the maximal optimal passive time are the same over randomized policies, which are mixtures of deterministic ones
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Theorem 1, (22)–(25), p.15; proof EC.3, pp.ec6–ec8

import Mathlib
import Definitions.Def_RelaxedIndexability_Arm
import Definitions.Def_RelaxedIndexability_Supplement_optimalValue
import Definitions.Def_RelaxedIndexability_Supplement_decisionBoundary
import Definitions.Def_RelaxedIndexability_Supplement_Indexable

open Matrix

namespace RelaxedIndexability.Supplement

/-- **Theorem 1** (Liu, arXiv:2107.11939v4, Theorem 1, p.15; proof EC.3, pp.ec6–ec8). Consider one
arm and `β ∈ (0, 1)`.

1. (22)–(23) For every belief `ω` in the simplex and every `m₀`, the passive times of the optimal
   single-arm policies from `ω` at subsidy `m₀` have a maximum `D_{β,m₀}(ω)`, and the right
   derivative of `m ↦ V_{β,m}(ω)` at `m₀` exists and equals it.
2. The arm is indexable iff for every `ω` and `m_ω` with `ω ∈ C(m_ω)` the right derivatives `d₀`
   and `d₁` at `m_ω` of `m ↦ V_{β,m}(ω; 0)` and `m ↦ V_{β,m}(ω; 1)` satisfy (24) `d₀ ≥ d₁`, and,
   if `d₀ = d₁`, there is `Δ > 0` with (25) `V_{β,m}(ω; 0) ≥ V_{β,m}(ω; 1)` for all
   `m ∈ (m_ω, m_ω + Δ)`.

**Formalization Note.** A right derivative is `HasDerivWithinAt` on `Set.Ioi`, which asserts
existence and determines the derivative. The interval of (25), printed `(m_ω + ∆m(ω))`, is
`(m_ω, m_ω + ∆m(ω))`, as the proof negates it in (EC.29), p.ec8. -/
theorem theorem_1 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (A : RelaxedIndexability.Arm) :
    (∀ ω ∈ stdSimplex ℝ (Fin A.K), ∀ m₀ : ℝ, ∃ D : ℝ,
      IsGreatest (optimalPassiveTimes β A.P A.B m₀ ω) D ∧
      HasDerivWithinAt (fun m => optimalValue β A.P A.B m ω) D (Set.Ioi m₀) m₀) ∧
    (ArmIndexable β A ↔
      ∀ (ω : Fin A.K → ℝ) (mω : ℝ), ω ∈ decisionBoundary β A.P A.B mω →
        ∃ d₀ d₁ : ℝ,
          HasDerivWithinAt (fun m => optimalActionValue β A.P A.B m false ω) d₀ (Set.Ioi mω) mω ∧
          HasDerivWithinAt (fun m => optimalActionValue β A.P A.B m true ω) d₁ (Set.Ioi mω) mω ∧
          d₁ ≤ d₀ ∧
          (d₀ = d₁ → ∃ Δ : ℝ, 0 < Δ ∧ ∀ m ∈ Set.Ioo mω (mω + Δ),
            optimalActionValue β A.P A.B m true ω ≤ optimalActionValue β A.P A.B m false ω)) := by sorry

end RelaxedIndexability.Supplement
