-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_trdeg_adjoin_eq_cRk_b84e0c0b014c
-- name    : P2M_GroundTheory_Heights__Heights_trdeg_adjoin_eq_cRk_b84e0c0b014c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:38.806613+00:00
-- url     : https://prove2.me/theorems/74baaf57-6d68-477d-9a64-8d3a91bb5d3c
-- title:
--   P2 M Ground Theory Heights  Heights trdeg adjoin eq c Rk b84e0c0b014c: P2 M Ground Theory Heights  Heights trdeg adjoin eq c Rk b84e0c0b014c
-- statement:
--   The P2 M Ground Theory Heights  Heights trdeg adjoin eq c Rk b84e0c0b014c construction uses the P2 M Ground Theory Heights  Heights trdeg adjoin eq c Rk b84e0c0b014c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTrdegAdjoinLe.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTrdegAdjoinLe.lean#L26-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegAdjoinLe
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
open Algebra Cardinal Set AlgebraicIndependent
noncomputable section
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem P2M_GroundTheory_Heights__Heights_trdeg_adjoin_eq_cRk_b84e0c0b014c (A : Set Ω) :
    Algebra.trdeg K (Algebra.adjoin K A) = (AlgebraicIndependent.matroid K Ω).cRk A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«trdeg_adjoin_eq_cRk» := P2M_GroundTheory_Heights__Heights_trdeg_adjoin_eq_cRk_b84e0c0b014c
