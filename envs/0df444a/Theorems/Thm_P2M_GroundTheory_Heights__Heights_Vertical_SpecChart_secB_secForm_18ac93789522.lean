-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_secForm_18ac93789522
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_secForm_18ac93789522
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:11.33405+00:00
-- url     : https://prove2.me/theorems/13fb6c78-842b-4c17-b30a-17b47d0bd350
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B sec Form 18ac93789522: P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B sec Form 18ac93789522
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B sec Form 18ac93789522 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B sec Form 18ac93789522 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L146-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L146-L155

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_secForm_18ac93789522 (i : Fin e) :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inl (i, m))) * toSecB e I v (X m) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«secB_secForm» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_secForm_18ac93789522
