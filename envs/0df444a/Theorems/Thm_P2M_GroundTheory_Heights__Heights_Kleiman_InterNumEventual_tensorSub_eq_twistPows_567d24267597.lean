-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_eq_twistPows_567d24267597
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_eq_twistPows_567d24267597
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:06.792322+00:00
-- url     : https://prove2.me/theorems/ff7b44dd-1909-4490-b016-ed6fce0c19f8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub eq twist Pows 567d24267597: P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub eq twist Pows 567d242675
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub eq twist Pows 567d24267597 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual tensor Sub eq twist Pows 567d24267597 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L83-L85

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_eq_twistPows_567d24267597 {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (twistSys k x 0).twistPows n L (ind T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumEventual».«tensorSub_eq_twistPows» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_tensorSub_eq_twistPows_567d24267597
