-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_smul__159faebf7988
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_smul__159faebf7988
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:34.658868+00:00
-- url     : https://prove2.me/theorems/cecec960-f161-43d6-a9e5-38572c851d8b
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt smul  159faebf7988: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt smul  159faebf7988
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt smul  159faebf7988 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt smul  159faebf7988 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L352-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L352-L354

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_smul__159faebf7988 (e : E) (x : S.V) : S.pt τ (e • x) = τ.embedding e • S.pt τ x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«pt_smul'» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_smul__159faebf7988
