-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_analyticAt_pullQ_ed8ee6f101e4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_analyticAt_pullQ_ed8ee6f101e4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:26.171075+00:00
-- url     : https://prove2.me/theorems/b5333ccd-cc84-52ec-a116-c47b0c5fe105
-- title:
--   P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds analytic At pull Q ed8ee6f101e4: P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds analytic At pull Q ed8ee6f101e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds analytic At pull Q ed8ee6f101e4 construction uses the P2 M Ground Theory Heights  Heights Inter pullback Bad Image holds analytic At pull Q ed8ee6f101e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DetRestrictScalarsEqZero.lean#L34-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DetRestrictScalarsEqZero.lean#L34-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DetRestrictScalarsEqZero
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
  Topology Filter
open GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_analyticAt_pullQ_ed8ee6f101e4 (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) (j : Fin R.A.n)
    (hj : x ∈ (R.A.chart j).source) (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullbackBadImage_holds».«analyticAt_pullQ» := P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_analyticAt_pullQ_ed8ee6f101e4
