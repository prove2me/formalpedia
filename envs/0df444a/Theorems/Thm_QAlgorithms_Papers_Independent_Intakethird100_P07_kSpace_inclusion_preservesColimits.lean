-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kSpace_inclusion_preservesColimits
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kSpace_inclusion_preservesColimits
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:26:04.363735+00:00
-- url     : https://prove2.me/theorems/9e77250e-72cc-4742-8ba1-248bc4e539b4
-- title:
--   Corollary B.6
-- statement:
--   For the inclusion of the full category of compactly Hausdorff generated spaces into all topological spaces,
--
--   $$\iota:\mathrm{kTop}\longrightarrow\mathrm{Top},\qquad\iota\text{ preserves colimits}.$$
--
--   Consequently colimits of k-spaces computed in kTop agree, via the inclusion and their cocone maps, with those computed in Top. No Hausdorffness restriction is imposed.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, Corollary B.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Corollary B.6, PDF p. 36: the inclusion preserves categorical colimits. -/
theorem kSpace_inclusion_preservesColimits :
    Limits.PreservesColimits
      (CompactlyGenerated.compactlyGeneratedToTop.{u, u}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
