-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_upward_and_meet_closed
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:35:23.073334+00:00
-- url     : https://prove2.me/theorems/162fe849-4260-4949-8092-5319c81e6f5d
-- title:
--   Proposition 3.4
-- statement:
--   In a bounded lattice $L$, every quasipoint $\mathfrak B$ is upward closed and closed under binary meets:
--
--   $$a\in\mathfrak B,\ a\le b\ \Longrightarrow\ b\in\mathfrak B,
--   \qquad a,b\in\mathfrak B\ \Longrightarrow\ a\wedge b\in\mathfrak B.$$
--
--   These are consequences of maximality; they are not included in the filter-base definition.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 39, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.4; de Groote, Observables I, PDF p./pp. 39.
-/
theorem quasipoint_upward_and_meet_closed {L : Type u} [Lattice L] [BoundedOrder L] (B : Set L) (hB : IsQuasipoint B) :
    (∀ a ∈ B, ∀ b : L, a ≤ b → b ∈ B) ∧
      (∀ a ∈ B, ∀ b ∈ B, a ⊓ b ∈ B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
