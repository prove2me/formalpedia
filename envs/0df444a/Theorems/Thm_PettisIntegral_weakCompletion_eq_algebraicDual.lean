-- Prove2me | Theorems.Thm_PettisIntegral_weakCompletion_eq_algebraicDual
-- name    : PettisIntegral.weakCompletion_eq_algebraicDual
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:26.147589+00:00
-- url     : https://prove2.me/theorems/c2be95b1-4baf-48d9-a2b7-2be64d4bbb95
-- title:
--   Lemma C.4.1.2 — the weak completion: $(E')^*$ with $\sigma((E')^*,E')$ is the completion of a Hausdorff locally convex space $E$ for its weak topology $\sigma(E,E')$
-- statement:
--   **The weak completion of a locally convex space (Lemma C.4.1.2).** Let $E$ be a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$, let $E'$ be its continuous dual, and let $(E')^*$ be the algebraic dual of $E'$ (all $\mathbb k$-linear forms on $E'$) with the topology $\sigma((E')^*,E')$ of pointwise convergence on $E'$. Let
--   $$\iota_E\colon E\longrightarrow(E')^*,\qquad \iota_E(u)(\varphi)=\varphi(u).$$
--   Then $(E')^*$ is the completion of $E$ for the weak topology $\sigma(E,E')$. Precisely:
--
--   1. $\iota_E$ is injective and $\sigma((E')^*,E')$ induces the weak topology $\sigma(E,E')$ on $E$: the map $\iota_E$ is a topological embedding of $(E,\sigma(E,E'))$ into $(E')^*$;
--   2. $\iota_E(E)$ is dense in $(E')^*$;
--   3. $(E')^*$ is complete for $\sigma((E')^*,E')$.
--
--   The space $(E')^*$ with this topology is the *weak completion* of $E$. It is the natural home of weak integrals: for a weakly integrable function $f\colon X\to E$ the linear form $\varphi\mapsto\int_X\varphi\circ f\,d\mu$ is always an element of $(E')^*$, and the question of Pettis integrability is whether it lies in the dense subspace $\iota_E(E)$.
--
--   **Formalization Note.** `toWeakCompletion 𝕜 u` (from `Def_PettisIntegral_Basic`) is the function $\varphi\mapsto\varphi(u)$ in the product space `StrongDual 𝕜 E → 𝕜`. The algebraic dual $(E')^*$ is the subset `{a | IsLinearMap 𝕜 a}` of this product, and $\sigma((E')^*,E')$ is the topology induced on it by the product topology. Part 1 is `Topology.IsEmbedding` on Mathlib's `WeakSpace 𝕜 E` (the space $E$ with $\sigma(E,E')$). Part 2 is stated as: the closure of the range of $\iota_E$ in the product space is exactly the set of linear forms (this says that $\iota_E(E)$ is dense in $(E')^*$ and that $(E')^*$ is closed in the product). Part 3 is `IsComplete` for the product uniformity, which induces on $(E')^*$ the uniformity of the topological vector space $((E')^*,\sigma((E')^*,E'))$. "Hausdorff locally convex" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]`; the source works over $\mathbb C$. The two further assertions of the lemma (closures of convex sets agree for the given and the weak topology; the normed case and the bidual) are available in Mathlib (`Convex.toWeakSpace_closure`, `NormedSpace.inclusionInDoubleDualLi`) and are not restated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 710, Lemma C.4.1.2 (first assertion), with Lemma C.4.1.1, p. 709, and Remark C.4.1.3; classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, 1.3 (density), and L. Narici and E. Beckenstein, Topological Vector Spaces, Theorem 8.2.9 (completeness), as cited in the paper's proof

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace PettisIntegral

/-- The weak completion: the canonical map of a Hausdorff locally convex space `E`, with its weak
topology, into the space of functions on its continuous dual is a topological embedding, the
closure of its range is the set of linear forms on the dual, and that set is complete. -/
theorem weakCompletion_eq_algebraicDual {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] :
    Topology.IsEmbedding
        (fun u : WeakSpace 𝕜 E => toWeakCompletion 𝕜 ((toWeakSpace 𝕜 E).symm u)) ∧
      closure (Set.range (fun u : E => toWeakCompletion 𝕜 u)) =
        {a : StrongDual 𝕜 E → 𝕜 | IsLinearMap 𝕜 a} ∧
      IsComplete {a : StrongDual 𝕜 E → 𝕜 | IsLinearMap 𝕜 a} := by sorry

end PettisIntegral
