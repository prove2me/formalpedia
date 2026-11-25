-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_weight_groupWeight_apply_bef25cb93b13
-- name    : P2M_GroundTheory_Heights__Heights_weight_groupWeight_apply_bef25cb93b13
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:32.915788+00:00
-- url     : https://prove2.me/theorems/3b2774d2-ea44-5f6b-b0fc-c53d2fdb2453
-- title:
--   P2 M Ground Theory Heights  Heights weight group Weight apply bef25cb93b13: P2 M Ground Theory Heights  Heights weight group Weight apply bef25cb93b13
-- statement:
--   The P2 M Ground Theory Heights  Heights weight group Weight apply bef25cb93b13 construction uses the P2 M Ground Theory Heights  Heights weight group Weight apply bef25cb93b13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L154-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L154-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {k n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_weight_groupWeight_apply_bef25cb93b13 (d : Fin k × Fin n →₀ ℕ) (i : Fin k) :
    Finsupp.weight (groupWeight k n) d i = Finsupp.weight (inGroup (n := n) i) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«weight_groupWeight_apply» := P2M_GroundTheory_Heights__Heights_weight_groupWeight_apply_bef25cb93b13
