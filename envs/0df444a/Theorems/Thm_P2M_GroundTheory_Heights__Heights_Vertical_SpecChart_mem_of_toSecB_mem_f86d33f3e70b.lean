-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toSecB_mem_f86d33f3e70b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toSecB_mem_f86d33f3e70b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:05:50.429302+00:00
-- url     : https://prove2.me/theorems/c5c30888-fa54-447b-a107-370a4806ac79
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Sec B mem f86d33f3e70b: P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Sec B mem f86d33f3e70b
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Sec B mem f86d33f3e70b construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Sec B mem f86d33f3e70b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L122-L128

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toSecB_mem_f86d33f3e70b [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {g : MvPolynomial (Fin n) (𝓞 K)}
    (hg : toSecB e I v g ∈ 𝔫) : g ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«mem_of_toSecB_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toSecB_mem_f86d33f3e70b
