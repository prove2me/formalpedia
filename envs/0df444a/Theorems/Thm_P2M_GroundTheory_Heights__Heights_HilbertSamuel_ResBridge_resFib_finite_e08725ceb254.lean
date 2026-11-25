-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resFib_finite_e08725ceb254
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resFib_finite_e08725ceb254
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:01.787087+00:00
-- url     : https://prove2.me/theorems/e30edd7d-7cec-4e12-90a7-2db3242c653f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Fib finite e08725ceb254: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Fib finite e08725ceb254
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Fib finite e08725ceb254 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge res Fib finite e08725ceb254 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L165-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L165-L174

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resFib_finite_e08725ceb254 {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (resProj R Ψ ⁻¹' {y} ∩
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0}).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«resFib_finite» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resFib_finite_e08725ceb254
