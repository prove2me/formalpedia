-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_quasiCompleteSpace_continuousMap
-- name    : VectorValuedHolomorphy.quasiCompleteSpace_continuousMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:23.079105+00:00
-- url     : https://prove2.me/theorems/2dcb4540-7ab6-45de-a8ea-74c0aedd46b4
-- title:
--   $C(X,E)$ with the topology of compact convergence is locally convex and quasi-complete when $X$ is locally compact and $E$ is quasi-complete
-- statement:
--   **Quasi-completeness of spaces of continuous vector-valued functions.**
--
--   Let $X$ be a locally compact Hausdorff space and let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$ (every closed bounded subset of $E$ is complete). Let $C(X,E)$ be the space of continuous functions $X\to E$ with the topology of uniform convergence on compact subsets, defined by the seminorms
--   $$q_{K,\nu}(f)=\sup_{x\in K}\nu(f(x)),$$
--   where $K$ runs over the compact subsets of $X$ and $\nu$ over the continuous seminorms of $E$.
--
--   Then $C(X,E)$ is a locally convex space which is quasi-complete: every closed bounded subset of $C(X,E)$ is complete. (It is also Hausdorff.)
--
--   This is the basic permanence property behind the function spaces of the paper: spaces of continuous, smooth or holomorphic functions with values in a quasi-complete space are again quasi-complete, so that vector-valued integrals and holomorphic functions with values in them behave well.
--
--   **Formalization Note.** `C(X, E)` is Mathlib's `ContinuousMap` with the compact-open topology and its uniform structure of compact convergence (`ContinuousMap.compactConvergenceUniformSpace`), which is the topology of the seminorms $q_{K,\nu}$. `E` carries `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E]`, and `X` is `[LocallyCompactSpace X] [T2Space X]`. The conclusion is the conjunction `PolynormableSpace ℂ C(X, E) ∧ QuasiCompleteSpace ℂ C(X, E)` (locally convex and quasi-complete, bounded meaning von Neumann bounded); the Hausdorff property of `C(X, E)` is already an instance in Mathlib and is not restated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 721, Lemma C.5.1.3(6) (proof on p. 722, by reduction to part (3), for which the paper cites N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §1, Corollary on p. III.4)

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem quasiCompleteSpace_continuousMap (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] (E : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] :
    PolynormableSpace ℂ C(X, E) ∧ QuasiCompleteSpace ℂ C(X, E) := by sorry

end VectorValuedHolomorphy
