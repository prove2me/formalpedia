-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___val_2c54f47722fa
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___val_2c54f47722fa
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:42.677717+00:00
-- url     : https://prove2.me/theorems/459c9e36-842b-40da-b8cf-c3c261c70d06
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart   val 2c54f47722fa: P2 M Ground Theory Heights  Heights Vertical Spec Chart   val 2c54f47722fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart   val 2c54f47722fa construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart   val 2c54f47722fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L209-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L209-L227

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___val_2c54f47722fa (hj : toSecB e I v (X j) ∉ 𝔫) (p : Par e n) : Φ hj (val e I j p) = parB e 𝔫 p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Φ_val» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___val_2c54f47722fa
