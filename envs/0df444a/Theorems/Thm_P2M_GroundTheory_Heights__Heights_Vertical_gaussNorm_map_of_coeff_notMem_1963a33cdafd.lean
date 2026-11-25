-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_of_coeff_notMem_1963a33cdafd
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_of_coeff_notMem_1963a33cdafd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:28.281816+00:00
-- url     : https://prove2.me/theorems/0ad5eec5-8961-4be3-8d19-7b8e0055f15d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical gauss Norm map of coeff not Mem 1963a33cdafd: P2 M Ground Theory Heights  Heights Vertical gauss Norm map of coeff not Mem 1963a33cdafd
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical gauss Norm map of coeff not Mem 1963a33cdafd construction uses the P2 M Ground Theory Heights  Heights Vertical gauss Norm map of coeff not Mem 1963a33cdafd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L49-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L49-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR
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
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_of_coeff_notMem_1963a33cdafd (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«gaussNorm_map_of_coeff_notMem» := P2M_GroundTheory_Heights__Heights_Vertical_gaussNorm_map_of_coeff_notMem_1963a33cdafd
