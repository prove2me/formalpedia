-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_SplitLinear_exists_minor_ne_zero_961d4111bb11
-- name    : P2M_GroundTheory_Heights__Theta_SplitLinear_exists_minor_ne_zero_961d4111bb11
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:55.338963+00:00
-- url     : https://prove2.me/theorems/4857024c-9195-4bac-acf8-15e738fd606a
-- title:
--   P2 M Ground Theory Heights  Theta Split Linear exists minor ne zero 961d4111bb11: P2 M Ground Theory Heights  Theta Split Linear exists minor ne zero 961d4111bb11
-- statement:
--   The P2 M Ground Theory Heights  Theta Split Linear exists minor ne zero 961d4111bb11 construction uses the P2 M Ground Theory Heights  Theta Split Linear exists minor ne zero 961d4111bb11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/SplitLinear/RankMinors.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/SplitLinear/RankMinors.lean#L20-L34

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

theorem P2M_GroundTheory_Heights__Theta_SplitLinear_exists_minor_ne_zero_961d4111bb11 {r c : Type*} [Fintype r] [Fintype c] (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ (I : Fin k → r) (J : Fin k → c), (P.submatrix I J).det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«SplitLinear».«exists_minor_ne_zero» := P2M_GroundTheory_Heights__Theta_SplitLinear_exists_minor_ne_zero_961d4111bb11
