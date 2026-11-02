-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_finite_type_iff_directed_meet_law
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.finite_type_iff_directed_meet_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:41:28.766972+00:00
-- url     : https://prove2.me/theorems/9239994a-1117-4438-b942-cf6bfa528809
-- title:
--   Lemma 3.2
-- statement:
--   A complete orthomodular lattice $L$ is of finite type exactly when meet with any fixed element preserves suprema of nonempty directed subsets:
--
--   $$a\wedge\bigvee S=\bigvee_{b\in S}(a\wedge b).$$
--
--   Here $S$ ranges over the directed ranges of arbitrary nonempty increasing nets. Finite type uses the closure of the corresponding union of Stone basic sets.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 46, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.2; de Groote, Observables I, PDF p./pp. 46.
-/
theorem finite_type_iff_directed_meet_law {L : Type u} [CompleteLattice L] (perp : L → L) (horth : IsOrthomodular perp) :
    IsFiniteType L ↔ HasDirectedMeetLaw L := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
