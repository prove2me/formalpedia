-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_of_succ_le_85c067b0ad94
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_of_succ_le_85c067b0ad94
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:26.829211+00:00
-- url     : https://prove2.me/theorems/bffe0bd6-8285-49a8-bda2-e7502a36780c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman with Bot le of succ le 85c067b0ad94: P2 M Ground Theory Heights  Heights Kleiman with Bot le of succ le 85c067b0ad94
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman with Bot le of succ le 85c067b0ad94 construction uses the P2 M Ground Theory Heights  Heights Kleiman with Bot le of succ le 85c067b0ad94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L115-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
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
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_of_succ_le_85c067b0ad94 {d : WithBot ℕ∞} {D : ℕ} (h : d + 1 ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ (D : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«withBot_le_of_succ_le» := P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_of_succ_le_85c067b0ad94
