-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutant_arbitrary_join_distribution
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_arbitrary_join_distribution
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:56:03.358849+00:00
-- url     : https://prove2.me/theorems/e361394f-e3a9-492d-837a-9803bedeff8f
-- title:
--   rem-2.2 (complete-lattice clause)
-- statement:
--   For a complete orthomodular lattice, every $a\in S$ distributes over every join from $S^C$, including empty families: $a\wedge\bigvee t=\bigvee_{b\in t}(a\wedge b)$.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 23, rem-2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-2.2; de Groote, Observables I, PDF pp. 23.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem commutant_arbitrary_join_distribution {L : Type u} [CompleteLattice L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) (a : L) (ha : a ∈ S)
    (t : Set L) (ht : t ⊆ latticeCommutant perp S) :
    a ⊓ sSup t = sSup ((fun b => a ⊓ b) '' t) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
