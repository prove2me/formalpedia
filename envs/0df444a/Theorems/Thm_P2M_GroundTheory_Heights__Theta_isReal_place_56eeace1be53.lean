-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isReal_place_56eeace1be53
-- name    : P2M_GroundTheory_Heights__Theta_isReal_place_56eeace1be53
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:25.50044+00:00
-- url     : https://prove2.me/theorems/8553afb7-f132-4041-981d-c46dd5ec4bf7
-- title:
--   P2 M Ground Theory Heights  Theta is Real place 56eeace1be53: P2 M Ground Theory Heights  Theta is Real place 56eeace1be53
-- statement:
--   The P2 M Ground Theory Heights  Theta is Real place 56eeace1be53 construction uses the P2 M Ground Theory Heights  Theta is Real place 56eeace1be53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L141-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/CMDatum.lean#L141-L141

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
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
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
variable (F E)
omit [NumberField F]
variable {F}

theorem P2M_GroundTheory_Heights__Theta_isReal_place_56eeace1be53 (v : InfinitePlace F) : v.IsReal := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isReal_place» := P2M_GroundTheory_Heights__Theta_isReal_place_56eeace1be53
