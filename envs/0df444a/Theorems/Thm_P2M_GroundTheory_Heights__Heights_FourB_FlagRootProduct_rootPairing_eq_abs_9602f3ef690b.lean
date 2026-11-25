-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_rootPairing_eq_abs_9602f3ef690b
-- name    : P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_rootPairing_eq_abs_9602f3ef690b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:22.574591+00:00
-- url     : https://prove2.me/theorems/98aa59c5-5ba6-4d9f-9e2f-5d7c7bf2cbd0
-- title:
--   P2 M Ground Theory Heights  Heights Four B Flag Root Product root Pairing eq abs 9602f3ef690b: P2 M Ground Theory Heights  Heights Four B Flag Root Product root Pairing eq abs 9602f3ef690b
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Flag Root Product root Pairing eq abs 9602f3ef690b construction uses the P2 M Ground Theory Heights  Heights Four B Flag Root Product root Pairing eq abs 9602f3ef690b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagRootProduct.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagRootProduct.lean#L7-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagRootProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB

theorem P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_rootPairing_eq_abs_9602f3ef690b {N p : ℕ} {lam : Fin N → ℝ}
    (hd : IsSplitDominant N p lam) (q : LowerPair N) :
    rootPairing N p lam q = |lam q.1.1 - lam q.1.2| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«FlagRootProduct».«rootPairing_eq_abs» := P2M_GroundTheory_Heights__Heights_FourB_FlagRootProduct_rootPairing_eq_abs_9602f3ef690b
