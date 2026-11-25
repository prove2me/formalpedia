-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resProj_eq_local_78e4d1ce2a23
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resProj_eq_local_78e4d1ce2a23
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:55.200747+00:00
-- url     : https://prove2.me/theorems/5a5b43ab-8dfa-5e7d-89ef-dc3b22f5812a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Proj eq local 78e4d1ce2a23: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Proj eq local 78e4d1ce2a23
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Proj eq local 78e4d1ce2a23 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Proj eq local 78e4d1ce2a23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L53-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resProj_eq_local_78e4d1ce2a23 (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x y : R.R.M}
    (hy : y ∈ R.R.src (R.idx x)) :
    resProj R Ψ y = fun i => Ψ (segre (R.liftAt x y)) i.succ / Ψ (segre (R.liftAt x y)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«resProj_eq_local» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resProj_eq_local_78e4d1ce2a23
