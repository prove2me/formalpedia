-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_borel_quasipoint_contains_open_quasipoint
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.borel_quasipoint_contains_open_quasipoint
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:47:47.335965+00:00
-- url     : https://prove2.me/theorems/d8f344f7-35af-4c3b-9ca6-e6a2b1640d61
-- title:
--   Proposition 3.19
-- statement:
--   In the standing Baire situation, a Borel quasipoint $C$ contains an open-set quasipoint if and only if it contains no boundary of an open set:
--
--   $$\exists\mathfrak B\in Q(T(M)),\ \mathfrak B\subseteq C
--   \quad\Longleftrightarrow\quad
--   \forall U\in T(M),\ \partial U\notin C.$$
--
--   For open $U$, the boundary is $\overline U\setminus U$; containment identifies opens with their Borel subsets.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 59, Proposition 3.19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.19; de Groote, Observables I, PDF p./pp. 59.
-/
theorem borel_quasipoint_contains_open_quasipoint {M : Type u} [TopologicalSpace M] [BaireSpace M]
    (C : StoneSpectrum (BorelSets M)) :
    (∃ B : StoneSpectrum (Opens M), ∀ U ∈ B.val, ∃ A ∈ C.val, A.val = (U : Set M)) ↔
    ∀ U : Opens M, ¬ ∃ A ∈ C.val, A.val = closure (U : Set M) \ (U : Set M) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
