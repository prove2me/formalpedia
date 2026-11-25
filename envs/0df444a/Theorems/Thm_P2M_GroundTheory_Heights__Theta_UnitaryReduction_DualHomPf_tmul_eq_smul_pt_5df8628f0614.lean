-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_tmul_eq_smul_pt_5df8628f0614
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_tmul_eq_smul_pt_5df8628f0614
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:57.125811+00:00
-- url     : https://prove2.me/theorems/90e1b9da-30be-500e-8b30-81f18b4510d6
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf tmul eq smul pt 5df8628f0614: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf tmul eq smul pt 5df8628f0614
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf tmul eq smul pt 5df8628f0614 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf tmul eq smul pt 5df8628f0614 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L362-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L362-L365

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_tmul_eq_smul_pt_5df8628f0614 (z : CAt τ.embedding) (v : S.V) :
    (z ⊗ₜ[E] v : S.FibSp τ) = (CAt.ofComplex τ.embedding).symm z • S.pt τ v := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«tmul_eq_smul_pt» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_tmul_eq_smul_pt_5df8628f0614
