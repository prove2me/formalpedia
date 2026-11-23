-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_mInt_congr
-- name    : ReciprocityTheory.AnForm.M.PLC.mInt_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:03.494818+00:00
-- url     : https://prove2.me/theorems/e8b1f871-dd50-4fb5-9487-ea2d1c9c9ca7
-- title:
--   PLC: m Int congr
-- statement:
--   The PLC construction uses the m Int congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveA.lean#L183-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveA.lean#L183-L194

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.PLC.mInt_congr (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (g g' : X → ℝ)
    (h : ∀ j, ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      g ((A.chart j).symm y) * locDens A Φ j y = g' ((A.chart j).symm y) * locDens A Ψ j y) :
    mInt A Φ g = mInt A Ψ g' := by sorry
