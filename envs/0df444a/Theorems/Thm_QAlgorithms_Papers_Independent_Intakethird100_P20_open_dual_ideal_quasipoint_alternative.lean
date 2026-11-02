-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_dual_ideal_quasipoint_alternative
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.open_dual_ideal_quasipoint_alternative
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:47:01.249316+00:00
-- url     : https://prove2.me/theorems/b3204f23-8232-418b-9cb2-f124e5d6b705
-- title:
--   Lemma 3.5
-- statement:
--   A proper dual ideal $J$ in the open-set lattice of any space $M$ is a quasipoint exactly when
--
--   $$\forall U\in T(M),\qquad U\in J\ \text{or}\ M\setminus\overline U\in J.$$
--
--   The second set is the open pseudocomplement, not the ordinary complement of $U$.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 58, Lemma 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.5; de Groote, Observables I, PDF p./pp. 58.
-/
theorem open_dual_ideal_quasipoint_alternative {M : Type u} [TopologicalSpace M] (J : Set (Opens M)) (hJ : IsDualIdeal J) :
    IsQuasipoint J ↔ ∀ U : Opens M, U ∈ J ∨ openPseudoCompl U ∈ J := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
