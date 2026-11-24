-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:55.587186+00:00
-- url     : https://prove2.me/theorems/cf2334a3-c468-4e74-8cf0-d20462c8fae6
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular analytic At chart 4620b31d9b76: P2 M Ground Theory Heights  Heights Targets Proj Regular analytic At chart 4620b31d9b76
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular analytic At chart 4620b31d9b76 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular analytic At chart 4620b31d9b76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L79-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegular.lean#L79-L94

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76 {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) (h0 : Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0) (j : Fin BV.n)
    (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegular».«analyticAt_chart» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76
