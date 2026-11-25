-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segre_lift_eq_smul_efc1b61b0f6d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_segre_lift_eq_smul_efc1b61b0f6d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:18.061646+00:00
-- url     : https://prove2.me/theorems/5b5a9d14-a9c1-460b-9ab8-e40ff17d0982
-- title:
--   P2 M Ground Theory Heights  Heights Targets segre lift eq smul efc1b61b0f6d: P2 M Ground Theory Heights  Heights Targets segre lift eq smul efc1b61b0f6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets segre lift eq smul efc1b61b0f6d construction uses the P2 M Ground Theory Heights  Heights Targets segre lift eq smul efc1b61b0f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L26-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem P2M_GroundTheory_Heights__Heights_Targets_segre_lift_eq_smul_efc1b61b0f6d {e : ℕ} (R : AnLogRes P J e) (x₀ : R.X) {x : R.X} (hx : x ∈ R.U x₀) :
    ∃ c : ℂ, c ≠ 0 ∧ segre (R.lift x x) = c • (segre (R.lift x₀ x) : ((k : K) → ι k) → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«segre_lift_eq_smul» := P2M_GroundTheory_Heights__Heights_Targets_segre_lift_eq_smul_efc1b61b0f6d
