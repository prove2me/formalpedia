-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_isSmoothHerm_ofWeight_e0b623fc4e1e
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_isSmoothHerm_ofWeight_e0b623fc4e1e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:29.0938+00:00
-- url     : https://prove2.me/theorems/9a9d4467-ed48-492d-b9c7-f20f75fdfb44
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear is Smooth Herm of Weight e0b623fc4e1e: P2 M Ground Theory Heights  Heights Points Bilinear is Smooth Herm of Weight e0b623fc4e1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear is Smooth Herm of Weight e0b623fc4e1e construction uses the P2 M Ground Theory Heights  Heights Points Bilinear is Smooth Herm of Weight e0b623fc4e1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L123-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_isSmoothHerm_ofWeight_e0b623fc4e1e {w : ((Σ k, ι k) → ℂ) → ℝ}
    (hw : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → w (fun p => c p.1 * z p) = w z)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (HermLine.ofWeight w hw) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«isSmoothHerm_ofWeight» := P2M_GroundTheory_Heights__Heights_PointsBilinear_isSmoothHerm_ofWeight_e0b623fc4e1e
