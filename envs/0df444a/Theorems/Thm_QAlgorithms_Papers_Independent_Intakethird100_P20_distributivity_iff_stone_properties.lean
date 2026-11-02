-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributivity_iff_stone_properties
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.distributivity_iff_stone_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:38:40.981754+00:00
-- url     : https://prove2.me/theorems/47f4ac47-7677-4b08-9b87-50e03c703990
-- title:
--   Proposition 3.5
-- statement:
--   For a bounded orthomodular lattice $L$, the following four conditions are equivalent: $L$ is distributive; $Q_a\cup Q_b=Q_{a\vee b}$ for all $a,b$; $Q_a\cup Q_{a^\perp}=Q(L)$ for all $a$; and every clopen subset of $Q(L)$ is a basic set. In particular,
--
--   $$L\text{ distributive}\quad\Longleftrightarrow\quad\operatorname{Clop}(Q(L))=\{Q_a:a\in L\}.$$
--
--   All four clauses are retained. Complementation of basic sets is not assumed in a general orthomodular lattice.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 44, Proposition 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.5; de Groote, Observables I, PDF p./pp. 44.
-/
theorem distributivity_iff_stone_properties {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) :
    (IsDistributive (L := L) ↔ ∀ a b : L, stoneBasic a ∪ stoneBasic b = stoneBasic (a ⊔ b)) ∧
    (IsDistributive (L := L) ↔ ∀ a : L, stoneBasic a ∪ stoneBasic (perp a) = Set.univ) ∧
    (IsDistributive (L := L) ↔ ∀ s : Set (StoneSpectrum L), IsClopen s → ∃ a : L, s = stoneBasic a) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
