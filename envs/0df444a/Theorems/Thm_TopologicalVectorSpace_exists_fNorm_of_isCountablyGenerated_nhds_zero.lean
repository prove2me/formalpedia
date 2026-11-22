-- Prove2me | Theorems.Thm_TopologicalVectorSpace_exists_fNorm_of_isCountablyGenerated_nhds_zero
-- name    : TopologicalVectorSpace.exists_fNorm_of_isCountablyGenerated_nhds_zero
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:24.782136+00:00
-- url     : https://prove2.me/theorems/23e0e2b3-b0d8-4361-9207-4de8afb788b5
-- title:
--   A Hausdorff topological vector space with a countable base of $0$-neighbourhoods has an F-norm: a translation-invariant metric with circled balls defining its topology
-- statement:
--   **Metrizable topological vector spaces carry a translation-invariant metric (existence of an F-norm).** Let $K$ be a non-discrete valued field (for instance $\mathbb R$ or $\mathbb C$) and let $E$ be a Hausdorff topological vector space over $K$ in which $0$ has a countable base of neighbourhoods. Then there is a function $|\cdot|\colon E\to\mathbb R$ (a *pseudo-norm*, or F-norm) such that
--
--   1. $|x|=0$ if and only if $x=0$;
--   2. $|x+y|\le|x|+|y|$ for all $x,y\in E$;
--   3. $|\lambda x|\le|x|$ for all $x\in E$ and all scalars $\lambda\in K$ with $|\lambda|\le 1$;
--   4. the sets $\{x\in E:\ |x|<\varepsilon\}$, $\varepsilon>0$, form a base of neighbourhoods of $0$ in $E$.
--
--   By 3 (with $\lambda=0$ and $\lambda=-1$) one has $|x|\ge 0$ and $|-x|=|x|$, so
--   $$d(x,y)=|x-y|$$
--   is a translation-invariant metric on $E$, and by 4 it induces the topology of $E$. In particular a Hausdorff topological vector space is metrizable if and only if it has a countable base of $0$-neighbourhoods, and then its topology is given by a translation-invariant metric whose balls centred at $0$ are circled.
--
--   The source recalls this at the start of §C.1.3 and uses the pseudo-norm to compare completeness in the sense of Cauchy sequences with completeness in the sense of Cauchy nets for metrizable spaces (in particular for Fréchet spaces).
--
--   **Formalization Note.** The statement asserts the existence of the function `N` with properties 1–4 rather than constructing a `MetricSpace` instance; property 4 is `Filter.HasBasis` for `𝓝 0`, which for a topological group is equivalent to the metric $d(x,y)=N(x-y)$ inducing the topology. The scalar field is any `NontriviallyNormedField`; the countability hypothesis is `(𝓝 (0 : E)).IsCountablyGenerated`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 658-659, opening paragraph of §C.1.3; classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. I, 6.1 (as cited by the paper)

import Mathlib

open Topology

set_option autoImplicit false

namespace TopologicalVectorSpace

theorem exists_fNorm_of_isCountablyGenerated_nhds_zero (𝕜 : Type*) {E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    (hE : (𝓝 (0 : E)).IsCountablyGenerated) :
    ∃ N : E → ℝ, (∀ x, N x = 0 ↔ x = 0) ∧ (∀ x y, N (x + y) ≤ N x + N y) ∧
      (∀ (c : 𝕜) (x : E), ‖c‖ ≤ 1 → N (c • x) ≤ N x) ∧
      (𝓝 (0 : E)).HasBasis (fun ε : ℝ => 0 < ε) (fun ε => {x | N x < ε}) := by sorry

end TopologicalVectorSpace
