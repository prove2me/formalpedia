-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_analyticAt_pullQ_ee2a81a860b3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_analyticAt_pullQ_ee2a81a860b3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:45.038193+00:00
-- url     : https://prove2.me/theorems/05164d8e-fc4e-5519-b112-c874cd02a5c5
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds analytic At pull Q ee2a81a860b3: P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds analytic At pull Q ee2a81a860
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds analytic At pull Q ee2a81a860b3 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Pushforward holds analytic At pull Q ee2a81a860b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L90-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/HasStrictFDerivAtEquiv.lean#L90-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_analyticAt_pullQ_ee2a81a860b3 (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackPushforward_holds».«analyticAt_pullQ» := P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_analyticAt_pullQ_ee2a81a860b3
