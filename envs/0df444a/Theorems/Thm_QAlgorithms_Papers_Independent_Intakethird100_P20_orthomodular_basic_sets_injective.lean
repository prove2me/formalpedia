-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthomodular_basic_sets_injective
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.orthomodular_basic_sets_injective
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:37:26.029599+00:00
-- url     : https://prove2.me/theorems/080adf5d-33d9-410d-88ce-da036f7be54c
-- title:
--   Lemma 3.1
-- statement:
--   In an orthomodular lattice with its designated orthocomplement, basic Stone sets distinguish lattice elements:
--
--   $$Q_a(L)=Q_b(L)\quad\Longrightarrow\quad a=b.$$
--
--   No distributivity or completeness assumption is added; the one-element lattice is allowed.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 43, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.1; de Groote, Observables I, PDF p./pp. 43.
-/
theorem orthomodular_basic_sets_injective {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) {a b : L} :
    stoneBasic a = stoneBasic b → a = b := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
