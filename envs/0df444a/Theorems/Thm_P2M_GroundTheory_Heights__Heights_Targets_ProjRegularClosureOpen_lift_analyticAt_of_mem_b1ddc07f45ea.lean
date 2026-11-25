-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_lift_analyticAt_of_mem_b1ddc07f45ea
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_lift_analyticAt_of_mem_b1ddc07f45ea
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:36.762797+00:00
-- url     : https://prove2.me/theorems/1585f0fb-6af1-551f-8a71-c03135dd807a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open lift analytic At of mem b1ddc07f45ea: P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open lift analytic At of me
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open lift analytic At of mem b1ddc07f45ea construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open lift analytic At of mem b1ddc07f45ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularClosureOpen.lean#L71-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularClosureOpen.lean#L71-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
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
open GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_lift_analyticAt_of_mem_b1ddc07f45ea {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (x : R.X) {j : Fin BV.n} {u : Fin n → ℂ}
    (hu : u ∈ (BV.chart j).target) (hU : ((BV.chart j).symm u).1 ∈ R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((BV.chart j).symm v).1) u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularClosureOpen».«lift_analyticAt_of_mem» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_lift_analyticAt_of_mem_b1ddc07f45ea
