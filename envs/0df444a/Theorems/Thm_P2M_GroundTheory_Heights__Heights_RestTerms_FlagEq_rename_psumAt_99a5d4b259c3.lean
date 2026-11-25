-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_psumAt_99a5d4b259c3
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_psumAt_99a5d4b259c3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:41.636867+00:00
-- url     : https://prove2.me/theorems/e9f28f68-012a-435e-a0c1-b2d1fb8df924
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename psum At 99a5d4b259c3: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename psum At 99a5d4b259c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename psum At 99a5d4b259c3 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq rename psum At 99a5d4b259c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L57-L61

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_psumAt_99a5d4b259c3 (f j k m : ℕ) (τ : Fin f) (w : Fin f → Equiv.Perm (Fin (j + k))) :
    rename (Equiv.prodCongrRight w) (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«rename_psumAt» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_psumAt_99a5d4b259c3
