-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_exists_open_quasipoint_over
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.exists_open_quasipoint_over
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T17:32:34.150946+00:00
-- url     : https://prove2.me/theorems/271cc41a-0f46-436e-963e-542079d7f905
-- title:
--   Every point of a Hausdorff space lies under an open quasipoint
-- statement:
--   Let $M$ be a Hausdorff topological space. Every $x\in M$ is represented by at least one quasipoint $B$ of the open-set lattice, in the sense that
--
--   $$\bigcap_{U\in B}\overline U=\{x\}.$$
--
--   This is the surjectivity ingredient for the canonical point map from the Stone spectrum. No compactness assumption on M is needed for this existence statement.
-- source:
--   Supporting existence lemma for H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.3, printed p.48 (PDF p.49), quasipoints over a point, and Corollary 3.5, printed p.55 (PDF p.56), canonical point map. The neighborhood filter-base extension uses Definition 3.3 and the Zorn extension preceding Definition 3.4, printed pp.37–38.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem exists_open_quasipoint_over {M : Type*} [TopologicalSpace M] [T2Space M]
    (x : M) : ∃ B : StoneSpectrum (Opens M), LiesOver B x := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
