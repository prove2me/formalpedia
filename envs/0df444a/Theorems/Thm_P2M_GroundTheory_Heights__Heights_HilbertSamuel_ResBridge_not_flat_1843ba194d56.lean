-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_not_flat_1843ba194d56
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_not_flat_1843ba194d56
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:28.352798+00:00
-- url     : https://prove2.me/theorems/a0847a08-e4ba-5d80-a5c1-9bbab5bcd343
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge not flat 1843ba194d56: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge not flat 1843ba194d56
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge not flat 1843ba194d56 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge not flat 1843ba194d56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullFlat.lean#L108-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullFlat.lean#L108-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_not_flat_1843ba194d56 {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n)
    {O : Set (Fin e → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«not_flat» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_not_flat_1843ba194d56
