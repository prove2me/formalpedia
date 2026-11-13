-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_quasipoint_cluster_characterization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.open_quasipoint_cluster_characterization
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T17:24:04.068134+00:00
-- url     : https://prove2.me/theorems/f02d7dfc-e7d3-42a3-8bd2-ef5b990bf8e0
-- title:
--   Cluster points of open quasipoints are exactly their underlying points
-- statement:
--   Let $M$ be a Hausdorff space, $B$ a quasipoint of its open-set lattice, and $x\in M$. The following conditions are equivalent:
--
--   $$\bigcap_{U\in B}\overline U=\{x\},\qquad x\in\bigcap_{U\in B}\overline U,\qquad\mathcal N_{\rm open}(x)\subseteq B.$$
--
--   Thus any cluster point of an open quasipoint uniquely determines its underlying point, and every open neighborhood of that point belongs to the quasipoint. This supports existence, surjectivity, and continuity of the canonical point map. No compactness is required for this characterization.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.3, printed p.48 (PDF p.49), paragraph immediately before Proposition 3.8: maximality gives every neighborhood and Hausdorff separation gives uniqueness. This isolates the cluster-point implication independently of the compactness used to obtain a cluster point.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem open_quasipoint_cluster_characterization {M : Type*} [TopologicalSpace M] [T2Space M]
    (B : StoneSpectrum (Opens M)) (x : M) :
    (LiesOver B x ↔ x ∈ ⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M)) ∧
    (LiesOver B x ↔ ∀ U : Opens M, x ∈ (U : Set M) → U ∈ B.val) := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
