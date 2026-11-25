-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_G_mem_fcc6df772951
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_G_mem_fcc6df772951
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:57.078982+00:00
-- url     : https://prove2.me/theorems/b5ad474c-1c33-4da2-ad3e-c5138ef85a90
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of G mem fcc6df772951: P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of G mem fcc6df772951
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of G mem fcc6df772951 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of G mem fcc6df772951 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L130-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L130-L137

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_G_mem_fcc6df772951 (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} [𝔫.IsMaximal] (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v}
    (hb : G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))) : b ∈ 𝔫 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«mem_of_G_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_G_mem_fcc6df772951
