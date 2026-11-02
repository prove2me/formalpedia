-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_boolean_quasipoint_upward_extension
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.boolean_quasipoint_upward_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:50:18.160207+00:00
-- url     : https://prove2.me/theorems/04b20bed-b4d0-469e-ad8e-e16a4baaaa32
-- title:
--   boolean-filter-upward-extension
-- statement:
--   Let $\beta$ be a Boolean quasipoint in an orthomodular lattice. If $c$ commutes with every member of $\beta$ and lies above some member, then
--
--   $$c\in\beta.$$
--
--   The commutation requirement is retained; ordinary upward closure is not asserted for a Boolean quasipoint in the whole ambient lattice.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 69, boolean-filter-upward-extension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- boolean-filter-upward-extension; de Groote, Observables I, PDF p./pp. 69.
-/
theorem boolean_quasipoint_upward_extension {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) (B : Set L) (hB : IsBooleanQuasipoint perp B)
    (c : L) (hcomm : ∀ a ∈ B, LatticeCommutes perp a c)
    (habove : ∃ b ∈ B, b ≤ c) : c ∈ B := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
