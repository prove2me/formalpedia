-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SplitLinear_exists_rows_linearIndependent_911acfd75589
-- name    : P2M_GroundTheory_Heights__Theta_SplitLinear_exists_rows_linearIndependent_911acfd75589
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:55.170396+00:00
-- url     : https://prove2.me/theorems/b2b7a7b0-1e13-4ec3-97a7-7ae0382685f7
-- title:
--   P2 M Ground Theory Heights  Theta Split Linear exists rows linear Independent 911acfd75589: P2 M Ground Theory Heights  Theta Split Linear exists rows linear Independent 911acfd75589
-- statement:
--   The P2 M Ground Theory Heights  Theta Split Linear exists rows linear Independent 911acfd75589 construction uses the P2 M Ground Theory Heights  Theta Split Linear exists rows linear Independent 911acfd75589 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/SplitLinear/RankMinors.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/SplitLinear/RankMinors.lean#L15-L18

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRowsLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.SplitLinear
open Matrix Module
universe u
variable {K : Type*} [Field K]

theorem P2M_GroundTheory_Heights__Theta_SplitLinear_exists_rows_linearIndependent_911acfd75589 {r : Type u} {c : Type*} [Fintype r] [Fintype c]
    (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ I : Fin k → r, LinearIndependent K (fun p => P (I p)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SplitLinear».«exists_rows_linearIndependent» := P2M_GroundTheory_Heights__Theta_SplitLinear_exists_rows_linearIndependent_911acfd75589
