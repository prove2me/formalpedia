-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_span_pt_a44c8735491c
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_span_pt_a44c8735491c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:07.750937+00:00
-- url     : https://prove2.me/theorems/d154b6b8-ccd7-5c9b-8514-a2222be4bbca
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem span pt a44c8735491c: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem span pt a44c8735491c
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem span pt a44c8735491c construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem span pt a44c8735491c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L402-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L402-L407

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_span_pt_a44c8735491c (y : S.FibSp τ) : y ∈ Submodule.span ℂ (Set.range (S.pt τ)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«mem_span_pt» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_span_pt_a44c8735491c
