-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthocomplement_complete_demorgan
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.orthocomplement_complete_demorgan
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:53:33.845608+00:00
-- url     : https://prove2.me/theorems/31234083-0093-4a00-bb26-14853e81ede4
-- title:
--   rem-2.1 (complete-lattice clause)
-- statement:
--   If the ortholattice is complete, orthocomplement interchanges arbitrary meets and joins, including empty families: $(\bigwedge s)^\perp=\bigvee_{a\in s}a^\perp$ and $(\bigvee s)^\perp=\bigwedge_{a\in s}a^\perp$.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 20, rem-2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-2.1; de Groote, Observables I, PDF pp. 20.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem orthocomplement_complete_demorgan {L : Type u} [CompleteLattice L]
    (perp : L → L) (hperp : IsOrthocomplement perp) :
    ∀ s : Set L, perp (sInf s) = sSup (perp '' s) ∧
      perp (sSup s) = sInf (perp '' s) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
