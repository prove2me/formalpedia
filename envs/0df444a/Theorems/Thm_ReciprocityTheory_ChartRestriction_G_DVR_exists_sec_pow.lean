-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_sec_pow
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_sec_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:44.962313+00:00
-- url     : https://prove2.me/theorems/d07bcbbb-fadb-5043-a40a-70b9ddab73e3
-- title:
--   DVR: exists sec pow
-- statement:
--   The DVR construction uses the exists sec pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L185-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L185-L208

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_sec_pow {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (hn : 1 ≤ n)
    (s : LB.Sec (LB.LinComb L (fun _ : Fin n => f) (fun _ => 1))) :
    ∃ s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => f) (fun _ => (n : ℤ))), nonzeroLocus s ≤ nonzeroLocus s' := by sorry
