-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_____bd9155de4351
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_____bd9155de4351
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:47.645589+00:00
-- url     : https://prove2.me/theorems/9a1a92a6-3506-49a2-855c-ae549030782f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart     bd9155de4351: P2 M Ground Theory Heights  Heights Vertical Spec Chart     bd9155de4351
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart     bd9155de4351 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart     bd9155de4351 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L229-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L229-L236

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_____bd9155de4351 (hj : toSecB e I v (X j) ∉ 𝔫) :
    (Φ hj).comp (σ e I j) = (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp
      ((algebraMap (ParDVR e n v) (SecB e I v)).comp (algebraMap _ (ParDVR e n v))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Φ_σ» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_____bd9155de4351
