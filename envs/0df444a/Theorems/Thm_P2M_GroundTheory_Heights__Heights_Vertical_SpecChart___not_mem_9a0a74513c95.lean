-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___not_mem_9a0a74513c95
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___not_mem_9a0a74513c95
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:04.089826+00:00
-- url     : https://prove2.me/theorems/34862ee9-ce96-499e-90a7-0b41a29b1514
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart   not mem 9a0a74513c95: P2 M Ground Theory Heights  Heights Vertical Spec Chart   not mem 9a0a74513c95
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart   not mem 9a0a74513c95 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart   not mem 9a0a74513c95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L29-L38

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___not_mem_9a0a74513c95 {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (s : MvPolynomial (Par e n) (𝓞 K))
    (hs : s ∈ (parPrime e n v).primeCompl) : σ e I j s ∉ Q e I j W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«σ_not_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___not_mem_9a0a74513c95
