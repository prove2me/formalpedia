-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_chartForm_dbede3e2003d
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_chartForm_dbede3e2003d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:46.166249+00:00
-- url     : https://prove2.me/theorems/25538d88-5c0a-484b-ba8e-b256e05caba3
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B chart Form dbede3e2003d: P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B chart Form dbede3e2003d
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B chart Form dbede3e2003d construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart sec B chart Form dbede3e2003d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L157-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L157-L166

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_chartForm_dbede3e2003d :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inr m)) * toSecB e I v (X m) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«secB_chartForm» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_chartForm_dbede3e2003d
