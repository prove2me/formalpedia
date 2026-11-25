-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_ext_pt_6623cc5f58f5
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_ext_pt_6623cc5f58f5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:54.789136+00:00
-- url     : https://prove2.me/theorems/13f23cb7-ac28-5f14-9909-1712b04bb82d
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf ext pt 6623cc5f58f5: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf ext pt 6623cc5f58f5
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf ext pt 6623cc5f58f5 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf ext pt 6623cc5f58f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L409-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L409-L416

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (S : MetSpace E) (τ : InfinitePlace E)

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_ext_pt_6623cc5f58f5 {M : Type} [AddCommGroup M] [Module ℂ M] {X Y : S.FibSp τ →ₗ[ℂ] M}
    (h : ∀ v, X (S.pt τ v) = Y (S.pt τ v)) : X = Y := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«ext_pt» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_ext_pt_6623cc5f58f5
