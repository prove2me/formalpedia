-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_scaleAll_mem_cc6c842d0898
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_scaleAll_mem_cc6c842d0898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:17.413072+00:00
-- url     : https://prove2.me/theorems/ce625ae9-e23b-468c-9fea-b421c3708576
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Zero Set scale All mem cc6c842d0898: P2 M Ground Theory Heights  Heights Segre Chart Zero Set scale All mem cc6c842d0898
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Zero Set scale All mem cc6c842d0898 construction uses the P2 M Ground Theory Heights  Heights Segre Chart Zero Set scale All mem cc6c842d0898 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartZeroSet.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartZeroSet.lean#L20-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.SegreChartZeroSet
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_scaleAll_mem_cc6c842d0898 (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : (fun p => c p.1 * z p) ∈ mcPts P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartZeroSet».«scaleAll_mem» := P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_scaleAll_mem_cc6c842d0898
