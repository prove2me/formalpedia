-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutant_complete_closure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_complete_closure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:54:47.741913+00:00
-- url     : https://prove2.me/theorems/acf182f4-58aa-4154-9069-7e7b972a08d4
-- title:
--   Proposition 2.2 (complete-lattice clause)
-- statement:
--   In a complete orthomodular lattice the commutant is closed under arbitrary ambient joins and meets. Thus its inherited order is complete; the empty join and meet are included.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 22, Proposition 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 2.2; de Groote, Observables I, PDF pp. 22.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem commutant_complete_closure {L : Type u} [CompleteLattice L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) :
    ∀ t : Set L, t ⊆ latticeCommutant perp S →
      sSup t ∈ latticeCommutant perp S ∧ sInf t ∈ latticeCommutant perp S := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
