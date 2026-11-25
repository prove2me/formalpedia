-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_contraction_and_flat_ed648f71ee55
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_contraction_and_flat_ed648f71ee55
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:25.57829+00:00
-- url     : https://prove2.me/theorems/7abb41f6-ce72-46d2-812b-2689078d7d1e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart contraction and flat ed648f71ee55: P2 M Ground Theory Heights  Heights Vertical Spec Chart contraction and flat ed648f71ee55
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart contraction and flat ed648f71ee55 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart contraction and flat ed648f71ee55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L276-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean#L276-L285

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_contraction_and_flat_ed648f71ee55 [W.IsPrime] (𝔫 : Ideal (SecB e I v)) [𝔫.IsMaximal]
    (hPW : integralModel I ≤ W) (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    (∀ g, toSecB e I v g ∈ 𝔫 → g ∈ W) ∧ RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«contraction_and_flat» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_contraction_and_flat_ed648f71ee55
