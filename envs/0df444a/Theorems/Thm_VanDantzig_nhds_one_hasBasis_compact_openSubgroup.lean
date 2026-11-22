-- Prove2me | Theorems.Thm_VanDantzig_nhds_one_hasBasis_compact_openSubgroup
-- name    : VanDantzig.nhds_one_hasBasis_compact_openSubgroup
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:10.537776+00:00
-- url     : https://prove2.me/theorems/8faef20d-dee1-4d08-a466-c6536c3f36d1
-- title:
--   Van Dantzig's theorem: a totally disconnected locally compact Hausdorff group has a neighbourhood base of the identity consisting of compact open subgroups
-- statement:
--   **Van Dantzig's theorem.** Let $G$ be a topological group (not necessarily abelian) whose topology is Hausdorff, locally compact and totally disconnected. Then the compact open subgroups of $G$ form a base of neighbourhoods of the neutral element $e$: every compact open subgroup is a neighbourhood of $e$, and for every neighbourhood $U$ of $e$ there is a subgroup $K\le G$ with
--   $$K\ \text{compact and open in } G,\qquad e\in K\subset U .$$
--
--   Such groups are often called locally profinite; examples are the additive and multiplicative groups of a non-archimedean local field, and the finite adeles and finite ideles of a number field. The theorem is the starting point of their harmonic analysis (smooth functions, Schwartz–Bruhat functions, Hecke algebras). The source uses it in the proof of Proposition A.5.2.3(1), to produce in every first countable locally profinite abelian group a decreasing sequence of compact open subgroups along which the maximal theorem and Lebesgue's differentiation theorem hold.
--
--   **Formalization Note.** The statement is `(𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G)) (fun K => (K : Set G))`: a subset of $G$ is a neighbourhood of $1$ if and only if it contains an open subgroup whose underlying set is compact. Mathlib has the corresponding statement only for compact groups (`IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`). The source applies the theorem to abelian groups; the classical theorem, formalized here, needs no commutativity.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 570, proof of Proposition A.5.2.3(1); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Thm. 4.1.6 and Prop. 4.1.5 (as cited by the paper)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace VanDantzig

theorem nhds_one_hasBasis_compact_openSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K : OpenSubgroup G => (K : Set G)) := by sorry

end VanDantzig
