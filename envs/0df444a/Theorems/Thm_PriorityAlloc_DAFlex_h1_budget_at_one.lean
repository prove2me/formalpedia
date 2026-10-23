-- Prove2me | Theorems.Thm_PriorityAlloc_DAFlex_h1_budget_at_one
-- name    : PriorityAlloc.DAFlex.h1_budget_at_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:15.034204+00:00
-- url     : https://prove2.me/theorems/fed5d90b-35a2-4d68-9c9e-62c173e26220
-- title:
--   Proof of Proposition H.1, p. 47 — the priority law (H.1) lives on [0,2]^n and, at cutoff 𝟏, yields budget set S with probability y_tS
-- statement:
--   Let $y \in Y^M$ and let $G_t$ be the priority law (H.1), $\pi_j = \mathbb{1}(j \in S) + \delta$ with $S \sim y_t$ and $\delta \sim \mathrm{Uniform}(0,1)$ independent. Then
--
--   1. each $G_t$ is a probability measure;
--   2. $G_t$-almost every priority lies in $\Pi = [0,2]^n$;
--   3. under the cutoff vector $\mathbf 1$, the budget set $B_\pi = \{j \in J : j = 0 \text{ or } \pi_j \ge 1\}$ of (H.3) satisfies
--   $$\mathbb{P}_{\pi \sim G_t}(B_\pi = S) = y_{tS} \qquad \text{for every segment } t \text{ and every } S \subseteq J.$$
--
--   In words: the mechanism with priorities (H.1) and cutoffs $\mathbf 1$ implements $y$, which is the benchmark $X$ against which the DA cutoff is compared in the proof of Proposition H.1.
-- source:
--   Shi, Optimal Priority-Based Allocation Mechanisms, SSRN manuscript 3425348 (June 2020; published Management Science 2022, doi:10.1287/mnsc.2020.3925), p. 47, proof of Proposition H.1, eq. (H.3) and 'the budget set is equal to S with probability exactly y_tS'

import Mathlib
import Definitions.Def_PriorityAlloc_DAFlex_Model

namespace PriorityAlloc.DAFlex

open MeasureTheory Classical

variable {m n : ℕ}

/-- Proof of Proposition H.1, p. 47: each priority law (H.1) is a probability measure on
`Π = [0,2]^n`, and under the cutoff vector `𝟏` the budget set (H.3) equals `S` with probability
exactly `y_{tS}`. -/
theorem h1_budget_at_one (M : Market m n) (y : Fin m → Finset (Option (Fin n)) → ℝ)
    (hy : Ymem M y) :
    (∀ t, IsProbabilityMeasure (h1Law y t)) ∧ (∀ t, ∀ᵐ π ∂(h1Law y t), π ∈ box 2) ∧
      ∀ t S, bsProb (h1Law y) 1 t S = y t S := by sorry

end PriorityAlloc.DAFlex
