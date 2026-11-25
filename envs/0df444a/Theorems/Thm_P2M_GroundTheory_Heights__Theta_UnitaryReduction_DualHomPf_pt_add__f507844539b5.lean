-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_add__f507844539b5
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_add__f507844539b5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:59.085796+00:00
-- url     : https://prove2.me/theorems/076dae4b-7e14-5e07-a247-bfb4fd28666a
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt add  f507844539b5: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt add  f507844539b5
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt add  f507844539b5 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt add  f507844539b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L348-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L348-L348

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_add__f507844539b5 (x y : S.V) : S.pt τ (x + y) = S.pt τ x + S.pt τ y := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«pt_add'» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_add__f507844539b5
