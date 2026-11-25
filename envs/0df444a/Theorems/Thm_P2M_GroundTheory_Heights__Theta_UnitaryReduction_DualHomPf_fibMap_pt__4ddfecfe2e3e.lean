-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_pt__4ddfecfe2e3e
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_pt__4ddfecfe2e3e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:03.114345+00:00
-- url     : https://prove2.me/theorems/e1f93a60-68f2-5cac-a8cc-baf3224b0875
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map pt  4ddfecfe2e3e: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map pt  4ddfecfe2e3e
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map pt  4ddfecfe2e3e construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map pt  4ddfecfe2e3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L418-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L418-L419

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_pt__4ddfecfe2e3e (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (v : S.V) :
    S.fibMap T φ τ (S.pt τ v) = T.pt τ (φ v) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«fibMap_pt'» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_pt__4ddfecfe2e3e
