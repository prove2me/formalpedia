-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_lattice_stone_compact
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.open_lattice_stone_compact
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:44:33.798582+00:00
-- url     : https://prove2.me/theorems/53ab4b01-76ae-4af2-8fdd-7fb078b08eee
-- title:
--   Corollary 3.4
-- statement:
--   For every topological space $M$, the Stone spectrum of its lattice of open sets is compact:
--
--   $$Q(T(M))\text{ is compact}.$$
--
--   No Hausdorff, compactness or nonemptiness assumption is imposed on $M$ itself.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 56, Corollary 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Corollary 3.4; de Groote, Observables I, PDF p./pp. 56.
-/
theorem open_lattice_stone_compact {M : Type u} [TopologicalSpace M] : CompactSpace (StoneSpectrum (Opens M)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
