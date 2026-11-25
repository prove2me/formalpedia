-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ptsIntegral_finset_sum_86d2d2f51bf7
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ptsIntegral_finset_sum_86d2d2f51bf7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:48.557154+00:00
-- url     : https://prove2.me/theorems/c6a550ba-af6c-5870-9457-8bcbdf590587
-- title:
--   P2 M Ground Theory Heights  Heights Targets pts Integral finset sum 86d2d2f51bf7: P2 M Ground Theory Heights  Heights Targets pts Integral finset sum 86d2d2f51bf7
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets pts Integral finset sum 86d2d2f51bf7 construction uses the P2 M Ground Theory Heights  Heights Targets pts Integral finset sum 86d2d2f51bf7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongSectionLimit.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongSectionLimit.lean#L46-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LogRegLineTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongSectionLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongChartLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongSectionLimit
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ptsIntegral_finset_sum_86d2d2f51bf7 (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Type*}
    (S : Finset T) {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t)) :
    ptsIntegral Q (pot L) (fun z => ∑ t ∈ S, u t z) = ∑ t ∈ S, ptsIntegral Q (pot L) (u t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ptsIntegral_finset_sum» := P2M_GroundTheory_Heights__Heights_Targets_ptsIntegral_finset_sum_86d2d2f51bf7
