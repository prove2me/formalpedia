-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_fact14
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.fact14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:43:46.148125+00:00
-- url     : https://prove2.me/theorems/3d28ad9e-06bd-4d92-8316-4a4f77340e7c
-- title:
--   Fact 14 and following paragraph: irreducibility
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   Both $M_N$ and $M_N^{(d)}$ are irreducible nonnegative matrices: for every pair of indices $i,j$ there is a strictly positive integer $q$ with
--
--   $$(M^q)_{ij}>0.$$
--
--   This gives the connectivity needed for Perron analysis, without an assumption about consecutive lexicographic indices.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 12, Fact 14 and following paragraph: irreducibility

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Fact 14 and its following paragraph, for the full matrix and physical
restrictions (PDF p.12). No adjacency of consecutive lexicographic shapes is assumed. -/
theorem fact14 {d N : ℕ} (hd : 0 < d) (hN : 0 < N) :
    (fullMatrix N).IsIrreducible ∧ (teleportMatrix d N).IsIrreducible := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
