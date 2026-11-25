-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resW_mem_fibre_b21b80029e59
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resW_mem_fibre_b21b80029e59
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:43.642025+00:00
-- url     : https://prove2.me/theorems/ac83fa3b-aa26-407a-bb77-1c0fbab99d66
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res W mem fibre b21b80029e59: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res W mem fibre b21b80029e59
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res W mem fibre b21b80029e59 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res W mem fibre b21b80029e59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L131-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L131-L150

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resW_mem_fibre_b21b80029e59 {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (hK : Nonempty K)
    (hPh : IsMultiHomogIdeal P) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) : resW R Ψ x ∈ fibre P Ψ (resProj R Ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«resW_mem_fibre» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resW_mem_fibre_b21b80029e59
