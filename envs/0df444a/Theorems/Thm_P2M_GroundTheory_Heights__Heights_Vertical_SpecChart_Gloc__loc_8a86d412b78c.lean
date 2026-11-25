-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Gloc__loc_8a86d412b78c
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Gloc__loc_8a86d412b78c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:10:35.810662+00:00
-- url     : https://prove2.me/theorems/f9880d18-0a47-4c88-b2ca-079b2f9e3960
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart Gloc  loc 8a86d412b78c: P2 M Ground Theory Heights  Heights Vertical Spec Chart Gloc  loc 8a86d412b78c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart Gloc  loc 8a86d412b78c construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart Gloc  loc 8a86d412b78c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L208-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L208-L215

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Gloc__loc_8a86d412b78c (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Gloc hσ hG).comp (Φloc hj hσ hG h𝔫) = RingHom.id _ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Gloc_Φloc» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Gloc__loc_8a86d412b78c
