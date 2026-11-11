-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_fact_3_17
-- name    : ParallelMatroidBasis.Main.fact_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:55.792066+00:00
-- url     : https://prove2.me/theorems/235045a3-b29e-4273-9bbe-2b140eb3f948
-- title:
--   Fact 3.17 — change of measure: $d_{KL}(\nu\|\pi)\le K$ and $\nu(G)\ge1/2$ give $\pi(G)\ge\frac14 2^{-2K}$
-- statement:
--   Let $\nu$ and $\pi$ be probability distributions on a space $\mathcal X$ with base-2 KL divergence $d_{KL}(\nu\|\pi)\le K$. If an event $G$ satisfies $\nu(G)\ge 1/2$, then
--   $$\pi(G)\ \ge\ \frac14\cdot 2^{-2K}.$$
--
--   A bound on relative entropy turns a large-probability event under $\nu$ into an event of non-negligible probability under $\pi$. In Theorem 4.1 it converts the KL bound of Corollary 3.16 into a lower bound on the probability that a random subsample keeps half of the density of a family. The paper cites it (Lemma 2.1 of [LVHV20]).
--
--   **Formalization Note.** $\nu,\pi$ are probability measures on an arbitrary measurable space and $G$ is measurable; the source's distributions on a set $\mathcal X$ are the special case of a countable space with its discrete σ-algebra. The real number $K$ is assumed nonnegative.
--
--   Differences from the source:
--   - generalization: distributions ν, π over a set X (KL as the sum of Definition 3.9) → probability measures on an arbitrary measurable space, a measurable event G, KL = Mathlib's klDiv / ln 2; reason: discrete distributions on a set with its discrete σ-algebra are a special case, on which klDiv / ln 2 is the sum of Definition 3.9, so the Lean statement specializes to the source's
--   - encoding: d_KL(ν∥π) ≤ K for a real K → 0 ≤ K and klBits ν π ≤ ENNReal.ofReal K; reason: KL divergence is nonnegative, so the source's hypothesis already forces K ≥ 0; stating 0 ≤ K excludes only the case K < 0, where ENNReal.ofReal K = 0 would otherwise make the hypothesis satisfiable
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Fact 3.17, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_KL

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Fact 3.17 (change of measure), PDF p.15 (printed p.13). Let `ν, π` be probability
distributions on `X` with `d_KL(ν‖π) ≤ K` (base 2). If an event `G` has `ν(G) ≥ 1/2`, then
`π(G) ≥ (1/4) · 2^{−2K}`. -/
theorem fact_3_17 {X : Type*} [MeasurableSpace X] (ν π : Measure X) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] (K : ℝ) (hK : 0 ≤ K) (hKL : klBits ν π ≤ ENNReal.ofReal K)
    (G : Set X) (hG : MeasurableSet G) (hνG : (1 / 2 : ENNReal) ≤ ν G) :
    ENNReal.ofReal (1 / 4 * (2 : ℝ) ^ (-2 * K)) ≤ π G := by sorry

end ParallelMatroidBasis.Main
