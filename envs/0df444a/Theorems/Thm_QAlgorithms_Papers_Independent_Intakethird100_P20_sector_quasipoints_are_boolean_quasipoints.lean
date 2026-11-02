-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_sector_quasipoints_are_boolean_quasipoints
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.sector_quasipoints_are_boolean_quasipoints
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:51:48.584085+00:00
-- url     : https://prove2.me/theorems/5209d7df-2404-4cf4-88d8-a0609c8d7ea2
-- title:
--   Proposition 3.24
-- statement:
--   For a Boolean sector $S$ of a complete orthomodular lattice, the proper ultrafilters of the Boolean algebra $S$ are exactly the Boolean quasipoints of the ambient lattice contained in $S$:
--
--   $$Q(S)=\{\beta\in Q^b(L):\beta\subseteq S\},$$
--
--   where subsets of $S$ are identified with their images in $L$. Sectors use the proof-intended sub-ortholattice convention. No topology on all Boolean quasipoints is introduced.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 69, Proposition 3.24

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.24; de Groote, Observables I, PDF p./pp. 69.
Source convention: Boolean sectors are maximal distributive sub-ortholattices; generation includes complements and bounds.
-/
theorem sector_quasipoints_are_boolean_quasipoints {L : Type u} [CompleteLattice L] (perp : L → L) (horth : IsOrthomodular perp)
    (S : Set L) (hS : IsBooleanSector perp S) :
    letI : Bot S := ⟨⟨⊥, hS.1.1⟩⟩
    ∀ B : Set S, IsQuasipoint B ↔ IsBooleanQuasipoint perp (Subtype.val '' B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
