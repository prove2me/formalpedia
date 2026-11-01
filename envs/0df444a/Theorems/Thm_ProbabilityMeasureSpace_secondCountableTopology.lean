-- Prove2me | Theorems.Thm_ProbabilityMeasureSpace_secondCountableTopology
-- name    : ProbabilityMeasureSpace.secondCountableTopology
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T10:42:16.43899+00:00
-- url     : https://prove2.me/theorems/2d834a84-3b57-4b3f-a12d-bf9e1b880c60
-- title:
--   Kechris Thm 17.23 — the weak topology on $P(X)$ is second countable for separable metrizable $X$
-- statement:
--   Let $X$ be a separable (pseudo-)metrizable topological space carrying its Borel $\sigma$-algebra, and let $P(X)$ be the space of Borel probability measures on $X$ with the topology of weak convergence (the coarsest topology making $\mu\mapsto\int f\,d\mu$ continuous for every bounded continuous $f$). Then $P(X)$ is second countable.
--
--   This is part of Kechris, Theorem 17.23: if $X$ is separable metrizable, so is $P(X)$ (Mathlib already provides metrizability through the Lévy–Prokhorov metric; separability, equivalently second countability for a metrizable space, is the missing part). The usual proof shows that the finitely supported measures $\sum_{k<N} r_k\delta_{d_k}$ with $d_k$ in a countable dense subset of $X$ and rational weights $r_k$ are dense in $P(X)$.
-- source:
--   A. S. Kechris, Classical Descriptive Set Theory (GTM 156, Springer 1995), §17.E, Theorem 17.23; also K. R. Parthasarathy, Probability Measures on Metric Spaces (1967), Ch. II, Theorem 6.2

import Mathlib

open MeasureTheory

/-- Kechris, Classical Descriptive Set Theory, Theorem 17.23: if `X` is separable metrizable,
then so is the space `P(X)` of Borel probability measures with the weak topology; in particular
`P(X)` is second countable. -/
theorem ProbabilityMeasureSpace.secondCountableTopology {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    SecondCountableTopology (ProbabilityMeasure X) := by sorry
