-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_maDens_comp_symm_eq_zero
-- name    : ReciprocityTheory.AnForm.M.PLC.maDens_comp_symm_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:58:07.307812+00:00
-- url     : https://prove2.me/theorems/2e903bf7-c233-48a5-8372-b87da52c4902
-- title:
--   PLC: ma Dens comp symm eq zero
-- statement:
--   The PLC construction uses the ma Dens comp symm eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveA.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveA.lean#L160-L168

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

theorem ReciprocityTheory.AnForm.M.PLC.maDens_comp_symm_eq_zero (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)) (v : X → ℝ)
    {y : Fin 1 → ℂ} (hy : y ∈ ψ.target) (hv : ψ.symm y ∉ tsupport v) :
    ReciprocityTheory.AnForm.maDens ![v ∘ ψ.symm] y = 0 := by sorry
