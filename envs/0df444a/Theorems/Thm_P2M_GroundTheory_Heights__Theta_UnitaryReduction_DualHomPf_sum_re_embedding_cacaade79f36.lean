-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_sum_re_embedding_cacaade79f36
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_sum_re_embedding_cacaade79f36
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:56.535526+00:00
-- url     : https://prove2.me/theorems/e8d423a3-eb30-491b-90cf-f4543da91383
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf sum re embedding cacaade79f36: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf sum re embedding cacaade79f36
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf sum re embedding cacaade79f36 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf sum re embedding cacaade79f36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L47-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L47-L70

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
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
open Classical

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_sum_re_embedding_cacaade79f36 (t : E) :
    ∑ τ : InfinitePlace E, (τ.embedding t).re = (Algebra.trace ℚ E t : ℝ) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«sum_re_embedding» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_sum_re_embedding_cacaade79f36
