-- Prove2me | Theorems.Thm_StrongOperatorTopology_metrizableSpace_of_isVonNBounded
-- name    : StrongOperatorTopology.metrizableSpace_of_isVonNBounded
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:16.592893+00:00
-- url     : https://prove2.me/theorems/f49ec741-3ed9-4662-a720-376b03259eca
-- title:
--   Lemma C.3.3.1(1) — on a separable Hilbert space, bounded sets of operators are metrizable for the strong operator topology
-- statement:
--   **Metrizability of bounded sets in the strong operator topology.**
--
--   Let $H$ be a complex Hilbert space and $\mathscr B(H)$ the space of bounded linear operators on $H$. The **strong operator topology** (SOT) on $\mathscr B(H)$ is the topology of pointwise convergence, defined by the seminorms
--   $$q_u(T)=\|T(u)\|_H,\qquad u\in H ;$$
--   write $\mathscr B_{\mathrm{SOT}}(H)$ for $\mathscr B(H)$ with this locally convex topology. A subset of $\mathscr B_{\mathrm{SOT}}(H)$ is bounded if every $q_u$ is bounded on it; by the uniform boundedness principle this is the same as being bounded for the operator norm.
--
--   Assume that $H$ is separable. Then every bounded subset $S$ of $\mathscr B_{\mathrm{SOT}}(H)$, with the topology induced by the strong operator topology, is metrizable.
--
--   The whole space $\mathscr B_{\mathrm{SOT}}(H)$ is not metrizable when $H$ is infinite-dimensional, so the restriction to bounded sets is essential. It allows one to argue with sequences on bounded sets of operators, for instance on the unitary group of a separable Hilbert space. In the paper it is recalled in §C.3.3, together with the quasi-completeness of $\mathscr B_{\mathrm{SOT}}(H)$ (part (2) of the lemma, not restated here), among the basic properties of the strong operator topology.
--
--   **Formalization Note.** $\mathscr B_{\mathrm{SOT}}(H)$ is Mathlib's `H →Lₚₜ[ℂ] H` (`PointwiseConvergenceCLM`), bounded means `Bornology.IsVonNBounded ℂ S` in that space, and the conclusion is `TopologicalSpace.MetrizableSpace S` for the subspace topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 697, Lemma C.3.3.1(1); classical reference: J. B. Conway, A Course in Functional Analysis, Springer, Graduate Texts in Mathematics 96 (the paper's [Cnw-a], listed in its bibliography as "A first Course in Functional Analysis"), Ch. IX, Prop. 1.3(e)

import Mathlib

open Filter Topology
set_option autoImplicit false

namespace StrongOperatorTopology

theorem metrizableSpace_of_isVonNBounded {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (S : Set (H →Lₚₜ[ℂ] H)) (hS : Bornology.IsVonNBounded ℂ S) :
    TopologicalSpace.MetrizableSpace S := by sorry

end StrongOperatorTopology
