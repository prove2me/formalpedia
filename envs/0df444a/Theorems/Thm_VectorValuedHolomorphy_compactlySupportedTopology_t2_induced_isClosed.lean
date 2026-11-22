-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_compactlySupportedTopology_t2_induced_isClosed
-- name    : VectorValuedHolomorphy.compactlySupportedTopology_t2_induced_isClosed
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:00.131853+00:00
-- url     : https://prove2.me/theorems/641fc126-959b-4bf4-a17f-1ec3adf973ae
-- title:
--   Lemma C.5.1.3(1) — $C_c(X,E)$ with the inductive limit topology is Hausdorff, induces uniform convergence on each $C(X,K;E)$, and each $C(X,K;E)$ is closed
-- statement:
--   **Basic properties of the inductive limit topology on $C_c(X,E)$ (Lemma C.5.1.3(1)).** Let $X$ be a locally compact Hausdorff space and $E$ a Hausdorff locally convex space over $\mathbb k\in\{\mathbb R,\mathbb C\}$. Let $C_c(X,E)$ be the space of continuous compactly supported functions $X\to E$ with the locally convex inductive limit topology of the subspaces $C(X,K;E)$ of functions with support in the compact set $K$, each with the topology of uniform convergence. Then:
--
--   1. $C_c(X,E)$ is Hausdorff;
--   2. for every compact $K\subset X$, the topology induced on $C(X,K;E)$ by $C_c(X,E)$ is the topology of uniform convergence;
--   3. for every compact $K\subset X$, the subspace $C(X,K;E)$ is closed in $C_c(X,E)$.
--
--   So the inductive limit is a strict one: the steps keep their own topologies and are closed. This is the starting point for the theory of the space $\mathscr K(X;E)$ (bounded sets, quasi-completeness, description of continuous linear maps such as vector measures).
--
--   **Formalization Note.** The topology is `VectorValuedHolomorphy.compactlySupportedTopology 𝕜 X E` from the definition file, a topology on Mathlib's `C_c(X, E)` that is not an instance and is therefore passed explicitly (`@T2Space C_c(X, E) (compactlySupportedTopology 𝕜 X E)`, `@IsClosed …`). $C(X,K;E)$ is the subtype `{f : C_c(X, E) // tsupport f ⊆ K}` (and the set `{f | tsupport f ⊆ K}` in the closedness statement); assertion 2 is the equality of two topologies on this subtype: the one induced by `Subtype.val` from `compactlySupportedTopology 𝕜 X E`, and the one induced by the inclusion into `C(X, E)` with the compact-open topology (uniform convergence on $X$, the supports being in the compact set $K$). "Hausdorff locally convex space over $\mathbb k$" is `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]` (`PolynormableSpace`: the topology is defined by a family of seminorms).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 721, Lemma C.5.1.3(1) (proof on p. 722); classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §1, Prop. 1(i) (as cited by the paper)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_CompactlySupportedInductiveLimit

open Filter Topology
open scoped CompactlySupported

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- The locally convex inductive limit topology on `C_c(X, E)` is Hausdorff; on the functions
supported in a compact set `K` it induces the topology of uniform convergence; and the set of
these functions is closed. -/
theorem compactlySupportedTopology_t2_induced_isClosed (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (E : Type*) [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] :
    @T2Space C_c(X, E) (compactlySupportedTopology 𝕜 X E) ∧
    ∀ K : Set X, IsCompact K →
      TopologicalSpace.induced (Subtype.val : {f : C_c(X, E) // tsupport f ⊆ K} → C_c(X, E))
          (compactlySupportedTopology 𝕜 X E) =
        TopologicalSpace.induced (fun f : {f : C_c(X, E) // tsupport f ⊆ K} => (f.1 : C(X, E)))
          ContinuousMap.compactOpen ∧
      @IsClosed C_c(X, E) (compactlySupportedTopology 𝕜 X E) {f | tsupport f ⊆ K} := by sorry

end VectorValuedHolomorphy
