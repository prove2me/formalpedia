-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_sub_04719375293b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_sub_04719375293b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:43.436144+00:00
-- url     : https://prove2.me/theorems/d51b1cde-35d3-50a9-998c-94034a14187f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub sub 04719375293b: P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub sub 04719375293b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub sub 04719375293b construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub sub 04719375293b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L74-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumEventual
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
open GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_sub_04719375293b {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = (twistSys k x 0).sub I * ∏ i, (L i).sub I ^ ind T i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumEventual».«tensorSub_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_sub_04719375293b
