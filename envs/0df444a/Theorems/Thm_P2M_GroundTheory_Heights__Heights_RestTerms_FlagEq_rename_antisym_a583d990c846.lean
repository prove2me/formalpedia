-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_antisym_a583d990c846
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_antisym_a583d990c846
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:50.30988+00:00
-- url     : https://prove2.me/theorems/4b093775-e0f2-4a5d-a39a-5d2fafabb91b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename antisym a583d990c846: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename antisym a583d990c846
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename antisym a583d990c846 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename antisym a583d990c846 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L72-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_antisym_a583d990c846 (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«rename_antisym» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_antisym_a583d990c846
