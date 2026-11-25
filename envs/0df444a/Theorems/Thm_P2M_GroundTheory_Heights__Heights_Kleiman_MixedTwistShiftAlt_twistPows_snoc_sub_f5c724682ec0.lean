-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_twistPows_snoc_sub_f5c724682ec0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_twistPows_snoc_sub_f5c724682ec0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:12.79916+00:00
-- url     : https://prove2.me/theorems/a21bc531-29b1-53ae-99fe-d8168e170d3b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt twist Pows snoc sub f5c724682ec0: P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt twist Pows snoc sub f5c724682ec0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt twist Pows snoc sub f5c724682ec0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Mixed Twist Shift Alt twist Pows snoc sub f5c724682ec0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PMixedTwistShift.lean#L43-L52

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_twistPows_snoc_sub_f5c724682ec0 {n : ℕ} (L : Fin n → LineBundle k x) (M : LineBundle k x) (T : Finset (Fin n))
    (m : ℕ) (I : Chart x) :
    ((twistSys k x 0).twistPows (n + 1)
        (fun j => (Fin.snoc (α := fun _ => LineBundle k x) L M j).toSubSystem)
        (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m)).sub I =
      M.sub I ^ m * (tensorSub (fun i => (L i).toSubSystem) T).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«MixedTwistShiftAlt».«twistPows_snoc_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_MixedTwistShiftAlt_twistPows_snoc_sub_f5c724682ec0
