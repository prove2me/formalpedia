-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_fibSub_fd4126231792
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_fibSub_fd4126231792
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:49.199313+00:00
-- url     : https://prove2.me/theorems/7700637f-f86e-5c02-8fba-3ac828ceeda0
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem fib Sub fd4126231792: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem fib Sub fd4126231792
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem fib Sub fd4126231792 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem fib Sub fd4126231792 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L582-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L582-L584

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_fibSub_fd4126231792 (S : MetSpace E) (τ : InfinitePlace E) (W : Submodule E S.V) {w : S.V}
    (hw : w ∈ W) : S.pt τ w ∈ S.fibSub W τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«pt_mem_fibSub» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_fibSub_fd4126231792
