-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymSample_eq_6e77b6491340
-- name    : P2M_GroundTheory_Heights__Heights_antisymSample_eq_6e77b6491340
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:00.701475+00:00
-- url     : https://prove2.me/theorems/f2a3a68d-d095-45c0-946a-0add225a17e7
-- title:
--   P2 M Ground Theory Heights  Heights antisym Sample eq 6e77b6491340: P2 M Ground Theory Heights  Heights antisym Sample eq 6e77b6491340
-- statement:
--   The P2 M Ground Theory Heights  Heights antisym Sample eq 6e77b6491340 construction uses the P2 M Ground Theory Heights  Heights antisym Sample eq 6e77b6491340 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L136-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_antisymSample_eq_6e77b6491340 : antisymSample =
    (X (0, 0) - X (0, 1)) * (X (0, 0) - X (0, 2)) * (X (0, 1) - X (0, 2)) *
      (X (0, 0) + X (0, 1) + X (0, 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«antisymSample_eq» := P2M_GroundTheory_Heights__Heights_antisymSample_eq_6e77b6491340
