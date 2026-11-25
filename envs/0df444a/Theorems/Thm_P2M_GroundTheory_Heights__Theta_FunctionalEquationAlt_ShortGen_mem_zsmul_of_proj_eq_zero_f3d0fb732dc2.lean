-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:33:35.610058+00:00
-- url     : https://prove2.me/theorems/e7b817b1-ab2a-5d48-89c7-df94846a03fa
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen mem zsmul of proj eq zero f3d0fb732dc2: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen mem zsmul of proj eq zer
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen mem zsmul of proj eq zero f3d0fb732dc2 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen mem zsmul of proj eq zero f3d0fb732dc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L141-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L141-L153

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2 {L : Submodule ℤ W} {v : W} (hvL : v ∈ L) (hv : v ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖) {y : W} (hy : y ∈ L) (h0 : proj v y = 0) :
    ∃ k : ℤ, y = k • v := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«mem_zsmul_of_proj_eq_zero» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2
