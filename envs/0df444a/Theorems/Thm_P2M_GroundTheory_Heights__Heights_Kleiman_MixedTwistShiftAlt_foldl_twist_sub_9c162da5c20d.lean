-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_foldl_twist_sub_9c162da5c20d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_foldl_twist_sub_9c162da5c20d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:45.900511+00:00
-- url     : https://prove2.me/theorems/4e18ea2a-33ab-5b39-99c8-145fdfe5026f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt foldl twist sub 9c162da5c20d: P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt foldl twist sub 9c162da5c20d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt foldl twist sub 9c162da5c20d construction uses the P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt foldl twist sub 9c162da5c20d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L22-L29

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_foldl_twist_sub_9c162da5c20d {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«MixedTwistShiftAlt».«foldl_twist_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_foldl_twist_sub_9c162da5c20d
