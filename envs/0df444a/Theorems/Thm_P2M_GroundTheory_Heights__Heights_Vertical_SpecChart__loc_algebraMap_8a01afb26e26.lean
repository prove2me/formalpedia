-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:07.418449+00:00
-- url     : https://prove2.me/theorems/2df38bd9-27a6-43b5-928f-9f67719d686f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart  loc algebra Map 8a01afb26e26: P2 M Ground Theory Heights  Heights Vertical Spec Chart  loc algebra Map 8a01afb26e26
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart  loc algebra Map 8a01afb26e26 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart  loc algebra Map 8a01afb26e26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L201-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L201-L206

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26 (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) :
    Φloc hj hσ hG h𝔫 (algebraMap _ _ c) = Φ hj c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Φloc_algebraMap» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart__loc_algebraMap_8a01afb26e26
