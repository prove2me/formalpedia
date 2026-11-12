-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutation_symmetric_iff_orthomodular
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.commutation_symmetric_iff_orthomodular
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:53:58.005053+00:00
-- url     : https://prove2.me/theorems/cecaa836-4d61-481e-a895-1c6357289c2e
-- title:
--   Proposition 2.1
-- statement:
--   For a bounded lattice with the designated orthocomplement, the relation $aCb\iff a=(a\wedge b)\vee(a\wedge b^\perp)$ is symmetric if and only if the lattice is orthomodular. Completeness is not assumed.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 21, Proposition 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 2.1; de Groote, Observables I, PDF pp. 21.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem commutation_symmetric_iff_orthomodular {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (hperp : IsOrthocomplement perp) :
    (∀ a b : L, LatticeCommutes perp a b → LatticeCommutes perp b a) ↔
      IsOrthomodular perp := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
