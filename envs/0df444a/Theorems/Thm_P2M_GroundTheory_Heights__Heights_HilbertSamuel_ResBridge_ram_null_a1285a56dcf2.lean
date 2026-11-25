-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_ram_null_a1285a56dcf2
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_ram_null_a1285a56dcf2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:33:15.331191+00:00
-- url     : https://prove2.me/theorems/6f0c4452-e2f8-5167-adcc-b5c5fd2a3dcb
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge ram null a1285a56dcf2: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge ram null a1285a56dcf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge ram null a1285a56dcf2 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge ram null a1285a56dcf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResBadNull.lean#L19-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PComponentResBadNull.lean#L19-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResBadNull
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
open GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_ram_null_a1285a56dcf2 {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' {x | Ψ (segre (R.pt x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.atlas.chart k).source ∧
        LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«ram_null» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_ram_null_a1285a56dcf2
