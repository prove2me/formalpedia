-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679
-- name    : P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:22.949023+00:00
-- url     : https://prove2.me/theorems/8e02946b-6796-479d-bbca-c70b9124609e
-- title:
--   P2 M Ground Theory Heights  Heights Four B sum fin split cast LE 158e19b9f679: P2 M Ground Theory Heights  Heights Four B sum fin split cast LE 158e19b9f679
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B sum fin split cast LE 158e19b9f679 construction uses the P2 M Ground Theory Heights  Heights Four B sum fin split cast LE 158e19b9f679 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L12-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
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
open Polynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679 {M : Type*} [AddCommMonoid M] {i N : ℕ} (hi : i ≤ N)
    (f : Fin N → M) :
    ∑ c, f c = ∑ c : Fin i, f (Fin.castLE hi c) + ∑ c, if i ≤ c.val then f c else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«sum_fin_split_castLE» := P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679
