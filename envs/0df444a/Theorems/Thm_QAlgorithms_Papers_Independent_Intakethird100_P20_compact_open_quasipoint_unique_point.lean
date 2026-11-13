-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_compact_open_quasipoint_unique_point
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.compact_open_quasipoint_unique_point
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T17:28:23.207347+00:00
-- url     : https://prove2.me/theorems/36f43dd3-c4c6-4153-a3ac-63af8a3d3adc
-- title:
--   Every open quasipoint on a compact Hausdorff space has a unique underlying point
-- statement:
--   Let $M$ be a compact Hausdorff space and let $B$ be a quasipoint of its open-set lattice. There is exactly one $x\in M$ for which
--
--   $$\bigcap_{U\in B}\overline U=\{x\}.$$
--
--   This makes the canonical point assignment from the Stone spectrum to M well defined. It separates the compactness-based existence argument from the Hausdorff cluster-point characterization.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.3, printed p.48 (PDF p.49), discussion before Proposition 3.8; Corollary 3.5, printed p.55 (PDF p.56), definition of the canonical point map for compact Hausdorff spaces.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem compact_open_quasipoint_unique_point {M : Type*} [TopologicalSpace M]
    [CompactSpace M] [T2Space M] (B : StoneSpectrum (Opens M)) :
    ∃! x : M, LiesOver B x := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
