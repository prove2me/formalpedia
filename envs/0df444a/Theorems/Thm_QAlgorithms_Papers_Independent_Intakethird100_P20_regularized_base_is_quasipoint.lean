-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_regularized_base_is_quasipoint
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.regularized_base_is_quasipoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:45:26.149955+00:00
-- url     : https://prove2.me/theorems/2499fdb1-3ce9-401c-8f61-86aa0b237a74
-- title:
--   Lemma 3.4
-- statement:
--   For every topological space $M$ and quasipoint $\mathfrak B\in Q(T(M))$, regularization produces a quasipoint in the regular-open Boolean algebra:
--
--   $$\mathfrak B^r=\{\operatorname{int}\overline U:U\in\mathfrak B\}\in Q(T_r(M)).$$
--
--   No separation, compactness or Baire hypothesis is imposed.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 56, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.4; de Groote, Observables I, PDF p./pp. 56.
-/
theorem regularized_base_is_quasipoint {M : Type u} [TopologicalSpace M] (B : StoneSpectrum (Opens M)) :
    IsQuasipoint (regularizedBase B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
