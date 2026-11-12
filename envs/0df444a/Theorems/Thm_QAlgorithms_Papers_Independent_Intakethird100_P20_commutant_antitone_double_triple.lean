-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutant_antitone_double_triple
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_antitone_double_triple
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:55:09.673211+00:00
-- url     : https://prove2.me/theorems/2c1dd00c-0baa-4379-b76e-e7fe89aeddb7
-- title:
--   Lemma 2.1
-- statement:
--   For subsets $S,T$ of an orthomodular lattice, $S\subseteq T$ implies $T^C\subseteq S^C$, every $S$ is contained in $S^{CC}$, and $S^C=S^{CCC}$. Both empty and nonempty subsets use the same commutant formula.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 23, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 2.1; de Groote, Observables I, PDF pp. 23.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem commutant_antitone_double_triple {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (horth : IsOrthomodular perp) (S T : Set L) :
    (S ⊆ T → latticeCommutant perp T ⊆ latticeCommutant perp S) ∧
    S ⊆ latticeCommutant perp (latticeCommutant perp S) ∧
    latticeCommutant perp S =
      latticeCommutant perp (latticeCommutant perp (latticeCommutant perp S)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
