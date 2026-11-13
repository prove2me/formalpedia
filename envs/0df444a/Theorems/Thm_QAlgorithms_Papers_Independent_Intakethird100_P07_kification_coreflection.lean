-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_coreflection
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_coreflection
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:25:36.642833+00:00
-- url     : https://prove2.me/theorems/31c7ef9b-8c3e-4fd6-b337-96c3a257d1d3
-- title:
--   Proposition B.5
-- statement:
--   Let $\mathrm{kTop}$ be the full category of compactly Hausdorff generated topological spaces, $\iota:\mathrm{kTop}\to\mathrm{Top}$ its inclusion, and $k$ the concrete functor obtained by putting the final compact-Hausdorff-probe topology on each underlying set and leaving each function unchanged. Then
--
--   $$\iota\dashv k.$$
--
--   In particular kTop is a coreflective full subcategory of Top. Both the space and probe universe are fixed explicitly in the formalization; spaces need not be Hausdorff.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, Proposition B.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Proposition B.5, PDF p. 36: the specified k functor is right adjoint
to the fully faithful inclusion of compactly generated spaces. -/
theorem kification_coreflection :
    Nonempty (CompactlyGenerated.compactlyGeneratedToTop.{u, u} ⊣
      kCoreflector.{u}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
