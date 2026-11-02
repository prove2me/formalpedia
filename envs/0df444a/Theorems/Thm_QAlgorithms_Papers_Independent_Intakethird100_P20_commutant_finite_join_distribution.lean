-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutant_finite_join_distribution
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_finite_join_distribution
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:55:35.83521+00:00
-- url     : https://prove2.me/theorems/684fbe87-60b7-4767-89e8-054fd0b93982
-- title:
--   rem-2.2
-- statement:
--   Every element $a$ of $S$ distributes over the join of a finite family in $S^C$: $a\wedge\bigvee b=\bigvee(a\wedge b)$. The empty family gives $a\wedge0=0$. Arbitrary families in a complete lattice are covered by the supporting statement.
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
theorem commutant_finite_join_distribution {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) (a : L) (ha : a ∈ S)
    {n : ℕ} (b : Fin n → L) (hb : ∀ i, b i ∈ latticeCommutant perp S) :
    a ⊓ Finset.univ.sup b = Finset.univ.sup (fun i => a ⊓ b i) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
