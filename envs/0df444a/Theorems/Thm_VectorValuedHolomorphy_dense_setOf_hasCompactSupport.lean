-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_dense_setOf_hasCompactSupport
-- name    : VectorValuedHolomorphy.dense_setOf_hasCompactSupport
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:43.386064+00:00
-- url     : https://prove2.me/theorems/ef04be51-8ada-4e96-ba0c-3b86d5c549b8
-- title:
--   Lemma C.5.1.3(5) — $C_c(X,E)$ is dense in $C(X,E)$ for the topology of uniform convergence on compact subsets
-- statement:
--   **Density of compactly supported functions (Lemma C.5.1.3(5)).** Let $X$ be a locally compact Hausdorff space and $E$ a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$. Let $C(X,E)$ be the space of continuous functions $X\to E$ with the topology of uniform convergence on compact subsets (defined by the seminorms $q_{K,\nu}(f)=\sup_{x\in K}\nu(f(x))$, $K\subset X$ compact, $\nu$ a continuous seminorm on $E$). Then the subspace $C_c(X,E)$ of compactly supported continuous functions is dense in $C(X,E)$:
--   $$\overline{C_c(X,E)}=C(X,E).$$
--
--   Concretely, for every continuous $f$, compact $K$ and continuous seminorm $\nu$ there is a compactly supported continuous $g$ with $g=f$ on $K$ (multiply $f$ by a continuous compactly supported function with values in $[0,1]$ equal to $1$ on $K$). The statement is used to extend by continuity constructions made on compactly supported functions.
--
--   **Formalization Note.** `C(X, E)` is Mathlib's `ContinuousMap` with the compact-open topology, which is the topology of uniform convergence on compact subsets; the subspace $C_c(X,E)$ is the set `{f : C(X, E) | HasCompactSupport f}` and the conclusion is `Dense` of this set. "Hausdorff locally convex space over $\mathbb k$" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]` (`PolynormableSpace`: the topology is defined by a family of seminorms); the field `𝕜` is an explicit argument since it occurs only in the hypotheses on `E`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 721, Lemma C.5.1.3(5) (proof on p. 722); classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §1, p. III.6, Prop. 4 (as cited by the paper)

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- For a locally compact Hausdorff space `X` and a Hausdorff locally convex space `E`, the
compactly supported continuous functions are dense in `C(X, E)` for the topology of uniform
convergence on compact subsets. -/
theorem dense_setOf_hasCompactSupport (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (E : Type*) [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] :
    Dense {f : C(X, E) | HasCompactSupport f} := by sorry

end VectorValuedHolomorphy
