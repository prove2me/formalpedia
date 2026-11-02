-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_quasipoint_dichotomy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.open_quasipoint_dichotomy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:41:53.202949+00:00
-- url     : https://prove2.me/theorems/be18bcf1-46df-4b5f-aba0-63e5ea2b575a
-- title:
--   Proposition 3.8
-- statement:
--   For a locally compact Hausdorff space $M$ and a quasipoint $\mathfrak B$ of its open-set lattice, exactly one of the following occurs: every complement of a compact set belongs to $\mathfrak B$; or there is a unique $x\in M$ with
--
--   $$\bigcap_{U\in\mathfrak B}\overline U=\{x\}.$$
--
--   These are respectively the unbounded quasipoints and the bounded quasipoints over a point. A bounded quasipoint need not equal the ordinary neighbourhood filter.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 49, Proposition 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.8; de Groote, Observables I, PDF p./pp. 49.
-/
theorem open_quasipoint_dichotomy {M : Type u} [TopologicalSpace M] [LocallyCompactSpace M] [T2Space M]
    (B : StoneSpectrum (Opens M)) :
    ((∀ K : Set M, IsCompact K → ∃ U ∈ B.val, (U : Set M) = Kᶜ) ∧
      ¬ ∃ x : M, LiesOver B x) ∨
    ((∃! x : M, LiesOver B x) ∧
      ¬ (∀ K : Set M, IsCompact K → ∃ U ∈ B.val, (U : Set M) = Kᶜ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
