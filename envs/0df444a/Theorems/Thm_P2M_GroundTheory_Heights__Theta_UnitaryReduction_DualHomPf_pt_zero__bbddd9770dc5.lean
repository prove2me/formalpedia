-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_zero__bbddd9770dc5
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_zero__bbddd9770dc5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:35.208787+00:00
-- url     : https://prove2.me/theorems/9cadc0de-1835-4260-81e4-f61f1fbde301
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt zero  bbddd9770dc5: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt zero  bbddd9770dc5
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt zero  bbddd9770dc5 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt zero  bbddd9770dc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L350-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L350-L350

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_zero__bbddd9770dc5 : S.pt τ 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«pt_zero'» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_zero__bbddd9770dc5
