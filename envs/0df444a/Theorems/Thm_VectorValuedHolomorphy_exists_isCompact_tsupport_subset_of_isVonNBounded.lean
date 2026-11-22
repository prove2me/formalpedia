-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_exists_isCompact_tsupport_subset_of_isVonNBounded
-- name    : VectorValuedHolomorphy.exists_isCompact_tsupport_subset_of_isVonNBounded
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:00.309645+00:00
-- url     : https://prove2.me/theorems/c1d68f98-9126-4561-90b8-44685d7b16da
-- title:
--   Lemma C.5.1.3(4) — for $X$ paracompact, every bounded subset of $C_c(X,E)$ is contained in some $C(X,K;E)$
-- statement:
--   **Bounded subsets of $C_c(X,E)$ have a common compact support (Lemma C.5.1.3(4)).** Let $X$ be a paracompact locally compact Hausdorff space and $E$ a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$. Let $C_c(X,E)$ carry the locally convex inductive limit topology of the subspaces $C(X,K;E)$ ($K\subset X$ compact) of functions supported in $K$. Then for every bounded subset $B\subset C_c(X,E)$ there is a compact $K\subset X$ with
--   $$B\subset C(X,K;E),$$
--   that is, $\operatorname{supp}(f)\subset K$ for all $f\in B$. (Then $B$ is bounded in $C(X,K;E)$ for the topology of uniform convergence, since $C_c(X,E)$ induces that topology on $C(X,K;E)$.)
--
--   This is the vector-valued form of the theorem of Dieudonné and Schwartz on bounded sets in strict inductive limits; a paracompact locally compact space is a topological sum of $\sigma$-compact spaces, which reduces the statement to a countable strict inductive limit and a locally convex direct sum. It is the key to the quasi-completeness of $C_c(X,E)$ and to the sequential description of its topology (a sequence converges if and only if it converges uniformly with supports in a fixed compact set).
--
--   **Formalization Note.** The topology is `VectorValuedHolomorphy.compactlySupportedTopology 𝕜 X E` from the definition file, passed explicitly: "bounded" is `@Bornology.IsVonNBounded 𝕜 C_c(X, E) _ _ _ (compactlySupportedTopology 𝕜 X E) B` (von Neumann bounded: absorbed by every neighbourhood of $0$). The conclusion is the existence of a compact `K : Set X` with `tsupport f ⊆ K` for all `f ∈ B`. "Hausdorff locally convex space over $\mathbb k$" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]` (`PolynormableSpace`: the topology is defined by a family of seminorms); paracompactness is `[ParacompactSpace X]`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 721, Lemma C.5.1.3(4) (proof on p. 722) and Remark C.5.1.4; classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §1, Prop. 2(ii) (as cited by the paper)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_CompactlySupportedInductiveLimit

open Filter Topology
open scoped CompactlySupported

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- If `X` is paracompact (locally compact Hausdorff), every bounded subset of `C_c(X, E)` for the
locally convex inductive limit topology consists of functions supported in one compact set. -/
theorem exists_isCompact_tsupport_subset_of_isVonNBounded (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ParacompactSpace X] (E : Type*)
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] (B : Set C_c(X, E))
    (hB : @Bornology.IsVonNBounded 𝕜 C_c(X, E) _ _ _ (compactlySupportedTopology 𝕜 X E) B) :
    ∃ K : Set X, IsCompact K ∧ ∀ f ∈ B, tsupport f ⊆ K := by sorry

end VectorValuedHolomorphy
