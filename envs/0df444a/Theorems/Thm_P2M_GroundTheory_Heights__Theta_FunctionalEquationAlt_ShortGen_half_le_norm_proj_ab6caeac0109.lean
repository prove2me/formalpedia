-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_half_le_norm_proj_ab6caeac0109
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_half_le_norm_proj_ab6caeac0109
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:22.011797+00:00
-- url     : https://prove2.me/theorems/42839acc-d380-4507-8654-00d599c1a49b
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen half le norm proj ab6caeac0109: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen half le norm proj ab6caeac0109
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen half le norm proj ab6caeac0109 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen half le norm proj ab6caeac0109 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L157-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L157-L179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [FiniteDimensional ℝ W]

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_half_le_norm_proj_ab6caeac0109 {L : Submodule ℤ W} {v : W} (hvL : v ∈ L) (hv : v ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖) {x : W} (hx : x ∈ L) (h0 : proj v x ≠ 0) :
    ‖v‖ / 2 ≤ ‖proj v x‖ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«half_le_norm_proj» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_half_le_norm_proj_ab6caeac0109
