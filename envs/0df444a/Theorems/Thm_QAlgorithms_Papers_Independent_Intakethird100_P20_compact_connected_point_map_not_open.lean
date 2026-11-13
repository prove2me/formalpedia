-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_compact_connected_point_map_not_open
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.compact_connected_point_map_not_open
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:44:07.220704+00:00
-- url     : https://prove2.me/theorems/3568914a-a42e-45a0-97a0-f5ec146d29d6
-- title:
--   compact-point-map-not-open
-- statement:
--   Let $M$ be a connected compact Hausdorff space with at least two points. Its canonical point map from $Q(T(M))$ is continuous, surjective and closed, but
--
--   $$\operatorname{pt}:Q(T(M))\to M\quad\text{is not open}.$$
--
--   The map is characterized by the singleton intersection of closures of each quasipoint's members. The nontriviality condition excludes the singleton exception.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 56, compact-point-map-not-open

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- compact-point-map-not-open; de Groote, Observables I, PDF p./pp. 56, 57.
-/
theorem compact_connected_point_map_not_open {M : Type u} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [Nontrivial M] :
    ∃ pt : StoneSpectrum (Opens M) → M, (∀ B, LiesOver B (pt B)) ∧
      Continuous pt ∧ Function.Surjective pt ∧ IsClosedMap pt ∧ ¬ IsOpenMap pt := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
