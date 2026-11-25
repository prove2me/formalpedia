-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_congr_pts_b0afe8eda56e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_congr_pts_b0afe8eda56e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:16.100161+00:00
-- url     : https://prove2.me/theorems/1576066f-a634-5ad9-a59e-b2f5373ce102
-- title:
--   P2 M Ground Theory Heights  Heights Inter pts Integral congr pts b0afe8eda56e: P2 M Ground Theory Heights  Heights Inter pts Integral congr pts b0afe8eda56e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pts Integral congr pts b0afe8eda56e construction uses the P2 M Ground Theory Heights  Heights Inter pts Integral congr pts b0afe8eda56e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PConsequences.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PConsequences.lean#L21-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_congr_pts_b0afe8eda56e (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ptsIntegral_congr_pts» := P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_congr_pts_b0afe8eda56e
