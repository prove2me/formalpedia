-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthocomplement_bounds_and_order
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.orthocomplement_bounds_and_order
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:53:14.45921+00:00
-- url     : https://prove2.me/theorems/4e7b3396-e19f-458e-a9f1-215d0af55b3e
-- title:
--   rem-2.1
-- statement:
--   In any bounded ortholattice the designated orthocomplement exchanges the bounds and reverses order: $0^\perp=1$, $1^\perp=0$, and $a\le b\iff b^\perp\le a^\perp$. The arbitrary-meet/join clause is the supporting statement for complete lattices.
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
theorem orthocomplement_bounds_and_order {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (hperp : IsOrthocomplement perp) :
    perp ⊥ = ⊤ ∧ perp ⊤ = ⊥ ∧ ∀ a b : L, a ≤ b ↔ perp b ≤ perp a := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
