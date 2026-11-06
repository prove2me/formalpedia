-- Prove2me | Theorems.Thm_SemiBanditSOO_eq_5_13
-- name    : SemiBanditSOO.eq_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:52.956717+00:00
-- url     : https://prove2.me/theorems/2daff787-e659-4470-ae1c-5d6785f92051
-- title:
--   (5.13) — $\sum_{t=1}^T\frac{I_{i,t}}{N_{i,t}+1}\le\sum_{k=1}^T\frac1k\le1+\log T$
-- statement:
--   Let $I_{i,t}$ indicate whether coordinate $i$ is revealed on an edge in round $t$ of Algorithm 1, and $N_{i,t}$ the number of rounds before round $t$ in which coordinate $i$ was revealed. For every coordinate $i$ and every realization,
--   $$\sum_{t=1}^T\frac{I_{i,t}}{N_{i,t}+1}\le\sum_{k=1}^T\frac1k\le1+\log T. \qquad (5.13)$$
--
--   This counting bound controls the sum of the per-stage bounds (5.12) over the rounds.
--
--   **Formalization Note.** A realization is a sequence of round vectors; $N_{i,t}$ is the number of samples of coordinate $i$ before round $t$.
--
--   Differences from the source:
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: ties in (3.5) broken in a fixed order → least maximizer for an arbitrary linear order on the node type (the statement holds for every order); reason: a fixed order is a linear order on the nodes
--   - encoding: Algorithm 1 run on T i.i.d. rounds X^1, …, X^T ∼ D, rounds t = 1, …, T → a deterministic function of ω = (X^1, …, X^T) under the product measure, rounds numbered 0, …, T − 1; reason: Algorithm 1 has no internal randomness; the same run
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, proof of Theorem 3.2, (5.13), p.25

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP
import Definitions.Def_SemiBanditSOO_Algorithm

open MeasureTheory

namespace SemiBanditSOO

open Classical in
/-- **(5.13): the harmonic count bound.** Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, proof of Theorem 3.2, (5.13),
p.25.

Let `I_{i,t}` indicate whether coordinate `i` is revealed on an edge in round `t` of Algorithm 1,
and `N_{i,t}` the number of rounds before round `t` in which coordinate `i` was revealed. For every
coordinate `i` and every realization,
`Σ_{t=1}^T I_{i,t}/(N_{i,t} + 1) ≤ Σ_{k=1}^T 1/k ≤ 1 + log T`.

**Formalization Note.** A realization is a sequence of round vectors `ω`; `N_{i,t}` is the length of
the sample list of coordinate `i` before round `t` (rounds `0, …, T − 1`). -/
theorem eq_5_13 {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} [Fintype V] [LinearOrder V]
    (Pb : Problem n dom V) (T : ℕ) (δ : ℝ) (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ω : Fin T → Obs dom) (i : Fin n) :
    ∑ t : Fin T, (if Pb.revealedOnEdge T δ ω t i then (1 : ℝ) else 0) /
        ((Pb.samplesAt (Lam n T δ) T ω t i).length + 1) ≤
      ∑ k ∈ Finset.Icc 1 T, (1 : ℝ) / k ∧
    ∑ k ∈ Finset.Icc 1 T, (1 : ℝ) / k ≤ 1 + Real.log T := by sorry

end SemiBanditSOO
