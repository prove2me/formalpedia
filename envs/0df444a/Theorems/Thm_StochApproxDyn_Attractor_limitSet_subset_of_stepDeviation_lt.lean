-- Prove2me | Theorems.Thm_StochApproxDyn_Attractor_limitSet_subset_of_stepDeviation_lt
-- name    : StochApproxDyn.Attractor.limitSet_subset_of_stepDeviation_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:25:22.465052+00:00
-- url     : https://prove2.me/theorems/dfa0393d-33af-4475-b4ac-74787e916262
-- title:
--   Lemma 6.8 — if $X(0)\in K\subset B(A)$ and $d_X(T)<\delta$ then $L(X)\subset A$
-- statement:
--   Let $\Phi$ be a semiflow on a **locally compact** metric space $M$, let $A\subset M$ be an attractor with basin $B(A)$, and let $K\subset B(A)$ be a nonempty compact set. Then there exist numbers $T>0$ and $\delta>0$, depending only on $K$ (and on $\Phi$ and $A$), such that for every asymptotic pseudotrajectory $X:\mathbb R_+\to M$ of $\Phi$,
--   $$X(0)\in K\ \text{ and }\ d_X(T)<\delta\quad\Longrightarrow\quad L(X)\subset A,$$
--   where $d_X(T)=\sup_{k\in\mathbb N}d(\Phi_T(X(kT)),X(kT+T))$ and $L(X)$ is the limit set of $X$.
--
--   A point of the basin is carried into $A$ by the flow; the lemma says the same holds for an asymptotic pseudotrajectory whose one-step errors over windows of length $T$ are uniformly small. It is the deterministic step in the proof of Theorem 7.3.
--
--   **Formalization Note** $T$ and $\delta$ are quantified before $X$, so they cannot depend on the trajectory. $d_X(T)$ is computed in `ℝ≥0∞`, and $d_X(T)<\delta$ is a strict inequality in `ℝ≥0∞`, i.e. exactly "the supremum is below $\delta$".
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 28, Section 6.3, Lemma 6.8 (with Eq. (23))

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics

open scoped NNReal ENNReal

namespace StochApproxDyn.Attractor

/-- Lemma 6.8 (Benaïm 1999, p. 28). -/
theorem limitSet_subset_of_stepDeviation_lt {M : Type*} [MetricSpace M] [LocallyCompactSpace M]
    (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (K : Set M) (hKne : K.Nonempty)
    (hK : IsCompact K) (hKB : K ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ X : ℝ≥0 → M, StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X → X 0 ∈ K →
        stepDeviation Φ X T < (δ : ℝ≥0∞) → StochApproxDyn.LimitSet.limitSet X ⊆ A := by sorry

end StochApproxDyn.Attractor
