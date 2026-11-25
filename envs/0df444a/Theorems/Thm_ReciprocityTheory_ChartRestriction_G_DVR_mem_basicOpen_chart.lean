-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_basicOpen_chart
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.mem_basicOpen_chart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:35.239406+00:00
-- url     : https://prove2.me/theorems/271911ba-e5ff-465a-99b4-23942fdc5bec
-- title:
--   DVR: mem basic Open chart
-- statement:
--   The DVR construction uses the mem basic Open chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L150-L158

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.mem_basicOpen_chart {M : LB Y} (s : LB.Sec M) {y : Y} {d j : M.ι} (hd : y ∈ Y.basicOpen (s.f d))
    (hj : y ∈ M.U j) : y ∈ Y.basicOpen (s.f j) := by sorry
