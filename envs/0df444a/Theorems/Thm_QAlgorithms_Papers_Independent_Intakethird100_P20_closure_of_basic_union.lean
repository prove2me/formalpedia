-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_closure_of_basic_union
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.closure_of_basic_union
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:39:45.800108+00:00
-- url     : https://prove2.me/theorems/e6186a7c-cf22-43e0-a6d6-fe7bc151a4c5
-- title:
--   closure-basic-union
-- statement:
--   For any family represented by a subset $S$ of a bounded lattice,
--
--   $$\mathfrak B\in\overline{\bigcup_{a\in S}Q_a}\quad\Longleftrightarrow\quad
--   \forall b\in\mathfrak B\ \exists a\in S:\ b\wedge a\ne0.$$
--
--   Empty families are allowed. The closure bar is essential. The complete-frame strengthening (3.4) is included in the separate Proposition 3.7 statement.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 45, closure-basic-union

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- closure-basic-union; de Groote, Observables I, PDF p./pp. 45.
-/
theorem closure_of_basic_union {L : Type u} [Lattice L] [BoundedOrder L] (s : Set L) (B : StoneSpectrum L) :
    (B ∈ closure (⋃ a ∈ s, stoneBasic a) ↔ ∀ b ∈ B.val, ∃ a ∈ s, b ⊓ a ≠ ⊥) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
