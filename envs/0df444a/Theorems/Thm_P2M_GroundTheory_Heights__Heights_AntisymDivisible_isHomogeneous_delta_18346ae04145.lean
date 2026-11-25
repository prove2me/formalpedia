-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_isHomogeneous_delta_18346ae04145
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_isHomogeneous_delta_18346ae04145
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:06.602766+00:00
-- url     : https://prove2.me/theorems/2a407091-67f5-409d-ae91-8052f66564ee
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible is Homogeneous delta 18346ae04145: P2 M Ground Theory Heights  Heights Antisym Divisible is Homogeneous delta 18346ae04145
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible is Homogeneous delta 18346ae04145 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible is Homogeneous delta 18346ae04145 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L240-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L240-L252

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
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
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_isHomogeneous_delta_18346ae04145 : (antisymDelta T N).IsHomogeneous (antisymDegree T N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«isHomogeneous_delta» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_isHomogeneous_delta_18346ae04145
