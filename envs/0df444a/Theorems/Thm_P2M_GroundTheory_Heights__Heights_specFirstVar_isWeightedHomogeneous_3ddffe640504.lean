-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirstVar_isWeightedHomogeneous_3ddffe640504
-- name    : P2M_GroundTheory_Heights__Heights_specFirstVar_isWeightedHomogeneous_3ddffe640504
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:55.588567+00:00
-- url     : https://prove2.me/theorems/e0d19399-6334-531b-a048-57f263e608b5
-- title:
--   P2 M Ground Theory Heights  Heights spec First Var is Weighted Homogeneous 3ddffe640504: P2 M Ground Theory Heights  Heights spec First Var is Weighted Homogeneous 3ddffe640504
-- statement:
--   The P2 M Ground Theory Heights  Heights spec First Var is Weighted Homogeneous 3ddffe640504 construction uses the P2 M Ground Theory Heights  Heights spec First Var is Weighted Homogeneous 3ddffe640504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSpecFirstHomog.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSpecFirstHomog.lean#L9-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSpecFirstHomog
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

theorem P2M_GroundTheory_Heights__Heights_specFirstVar_isWeightedHomogeneous_3ddffe640504 {k n : ℕ} (u : Fin n → ℂ) (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«specFirstVar_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_specFirstVar_isWeightedHomogeneous_3ddffe640504
