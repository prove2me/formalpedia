-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_quotToBn_flat_71bcdd64c091
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_quotToBn_flat_71bcdd64c091
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:05:16.235961+00:00
-- url     : https://prove2.me/theorems/438426a4-b7b5-59a7-b595-b6dbd9510024
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart quot To Bn flat 71bcdd64c091: P2 M Ground Theory Heights  Heights Vertical Spec Chart quot To Bn flat 71bcdd64c091
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart quot To Bn flat 71bcdd64c091 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart quot To Bn flat 71bcdd64c091 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L245-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L245-L272

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}
variable [(Q e I j W).IsPrime]
variable {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_quotToBn_flat_71bcdd64c091 (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«quotToBn_flat» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_quotToBn_flat_71bcdd64c091
