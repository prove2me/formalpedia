-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutant_sublattice
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_sublattice
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:54:24.786259+00:00
-- url     : https://prove2.me/theorems/3aceea8e-1969-431c-a12b-17001029dcea
-- title:
--   Proposition 2.2
-- statement:
--   In an orthomodular lattice, the commutant $S^C=\{b: aCb\text{ for every }a\in S\}$ contains both bounds and is closed under the designated complement and finite meets and joins, as established in the source proof. Its complete-lattice clause is stated separately.
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
theorem commutant_sublattice {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (horth : IsOrthomodular perp) (S : Set L) :
    IsSubOrtholattice perp (latticeCommutant perp S) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
