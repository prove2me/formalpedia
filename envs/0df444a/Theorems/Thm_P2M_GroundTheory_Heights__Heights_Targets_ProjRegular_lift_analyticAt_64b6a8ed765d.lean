-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:46.512927+00:00
-- url     : https://prove2.me/theorems/d462f50d-147e-48ec-9009-b5789a3cda27
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular lift analytic At 64b6a8ed765d: P2 M Ground Theory Heights  Heights Targets Proj Regular lift analytic At 64b6a8ed765d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular lift analytic At 64b6a8ed765d construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular lift analytic At 64b6a8ed765d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L38-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L38-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) {j : Fin BV.n} (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ R.U x.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegular».«lift_analyticAt» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
