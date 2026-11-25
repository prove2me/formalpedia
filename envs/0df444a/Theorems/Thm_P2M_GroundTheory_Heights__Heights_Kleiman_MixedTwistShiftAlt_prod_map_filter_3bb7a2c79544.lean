-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_prod_map_filter_3bb7a2c79544
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_prod_map_filter_3bb7a2c79544
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:46.890812+00:00
-- url     : https://prove2.me/theorems/68b55032-43b7-561c-a79e-242588b4876b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt prod map filter 3bb7a2c79544: P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt prod map filter 3bb7a2c79544
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt prod map filter 3bb7a2c79544 construction uses the P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt prod map filter 3bb7a2c79544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PMixedTwistShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.MixedTwistShiftAlt
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_prod_map_filter_3bb7a2c79544 {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«MixedTwistShiftAlt».«prod_map_filter» := P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_prod_map_filter_3bb7a2c79544
