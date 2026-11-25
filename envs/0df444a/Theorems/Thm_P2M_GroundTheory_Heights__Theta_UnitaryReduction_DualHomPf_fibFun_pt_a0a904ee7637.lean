-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibFun_pt_a0a904ee7637
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibFun_pt_a0a904ee7637
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:38.287895+00:00
-- url     : https://prove2.me/theorems/cfeedb84-88ec-5f3c-a3fb-1bcdc3ba070e
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Fun pt a0a904ee7637: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Fun pt a0a904ee7637
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Fun pt a0a904ee7637 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Fun pt a0a904ee7637 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L435-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L435-L439

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibFun_pt_a0a904ee7637 (σ : S.V →ₗ[E] E) (v : S.V) :
    fibFun S τ σ (S.pt τ v) = τ.embedding (σ v) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«fibFun_pt» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibFun_pt_a0a904ee7637
