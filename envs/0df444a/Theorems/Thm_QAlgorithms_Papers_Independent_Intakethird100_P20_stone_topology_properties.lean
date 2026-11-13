-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.stone_topology_properties
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:36:41.598718+00:00
-- url     : https://prove2.me/theorems/6bc664d0-51ff-41ed-967d-4a5cd1d0080f
-- title:
--   stone-topology-properties
-- statement:
--   For a bounded lattice $L$, the membership sets form a clopen basis for $Q(L)$ and satisfy
--
--   $$Q_{a\wedge b}=Q_a\cap Q_b,\qquad Q_0=\varnothing,\qquad Q_1=Q(L).$$
--
--   The Stone spectrum is Hausdorff, zero-dimensional and completely regular. No compactness is asserted for an arbitrary lattice.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 40, stone-topology-properties

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- stone-topology-properties; de Groote, Observables I, PDF p./pp. 40.
-/
theorem stone_topology_properties {L : Type u} [Lattice L] [BoundedOrder L] :
    (∀ a b : L, stoneBasic (a ⊓ b) = stoneBasic a ∩ stoneBasic b) ∧
    stoneBasic (⊥ : L) = ∅ ∧ stoneBasic (⊤ : L) = Set.univ ∧
    (∀ a : L, IsClopen (stoneBasic a)) ∧
    TopologicalSpace.IsTopologicalBasis (Set.range (stoneBasic : L → Set (StoneSpectrum L))) ∧
    TopologicalSpace.IsTopologicalBasis {s : Set (StoneSpectrum L) | IsClopen s} ∧
    T2Space (StoneSpectrum L) ∧ CompletelyRegularSpace (StoneSpectrum L) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
