-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cinv_mul_adb95d831303
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cinv_mul_adb95d831303
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:18.183824+00:00
-- url     : https://prove2.me/theorems/85dc2a88-02bd-4c63-8175-9514dcbef386
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart   cinv mul adb95d831303: P2 M Ground Theory Heights  Heights Vertical Spec Chart   cinv mul adb95d831303
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart   cinv mul adb95d831303 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart   cinv mul adb95d831303 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L205-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L205-L207

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
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
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}
variable {v : HeightOneSpectrum (𝓞 K)}
variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]
variable {e j 𝔫}

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cinv_mul_adb95d831303 (hj : toSecB e I v (X j) ∉ 𝔫) :
    Φ hj (cinv e I j) * algebraMap _ _ (toSecB e I v (X j)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Φ_cinv_mul» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cinv_mul_adb95d831303
