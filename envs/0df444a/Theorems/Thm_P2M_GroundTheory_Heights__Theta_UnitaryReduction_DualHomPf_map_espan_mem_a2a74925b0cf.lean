-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_espan_mem_a2a74925b0cf
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_espan_mem_a2a74925b0cf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:53.618305+00:00
-- url     : https://prove2.me/theorems/4d53234b-6801-5a37-ac5f-8b295b8930c7
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map espan mem a2a74925b0cf: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map espan mem a2a74925b0cf
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map espan mem a2a74925b0cf construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map espan mem a2a74925b0cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L545-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L545-L551

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
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_espan_mem_a2a74925b0cf (A : Submodule (𝓞 E) V) (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V')
    (hU : ∀ a ∈ A, U a ∈ espan B) {x : V} (hx : x ∈ espan A) : U x ∈ espan B := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«map_espan_mem» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_espan_mem_a2a74925b0cf
