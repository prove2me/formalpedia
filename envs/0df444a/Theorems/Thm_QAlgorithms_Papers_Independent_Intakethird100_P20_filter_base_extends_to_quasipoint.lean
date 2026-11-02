-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.filter_base_extends_to_quasipoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:35:58.555661+00:00
-- url     : https://prove2.me/theorems/28af2554-b929-4f38-a906-baa9ff52c58c
-- title:
--   quasipoint-extension
-- statement:
--   Every proper nonempty filter base $B$ in a bounded lattice $L$ extends to a quasipoint:
--
--   $$\exists\mathfrak B\in Q(L),\qquad B\subseteq\mathfrak B.$$
--
--   This supplies existence from the base itself rather than adding existence of quasipoints as a hypothesis.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 39, quasipoint-extension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- quasipoint-extension; de Groote, Observables I, PDF p./pp. 39.
-/
theorem filter_base_extends_to_quasipoint {L : Type u} [Lattice L] [BoundedOrder L] (B : Set L) (hB : IsFilterBase B) :
    ∃ C : Set L, IsQuasipoint C ∧ B ⊆ C := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
