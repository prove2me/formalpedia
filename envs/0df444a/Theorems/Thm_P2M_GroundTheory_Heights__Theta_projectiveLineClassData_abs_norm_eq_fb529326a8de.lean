-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:42.965992+00:00
-- url     : https://prove2.me/theorems/77df8fdd-9ac5-41a9-b3ff-0d6a6b721b43
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data abs norm eq fb529326a8de: P2 M Ground Theory Heights  Theta projective Line Class Data abs norm eq fb529326a8de
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data abs norm eq fb529326a8de construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data abs norm eq fb529326a8de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L54-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (x : K) : |((Algebra.norm ℚ x : ℚ) : ℝ)| = ‖σ x‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«abs_norm_eq» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_abs_norm_eq_fb529326a8de
