-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_gram_eq_801d9bae3823
-- name    : P2M_GroundTheory_Heights__Heights_FourB_gram_eq_801d9bae3823
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:23.728168+00:00
-- url     : https://prove2.me/theorems/cbd3f028-2136-4b58-a900-ab9ff8b29792
-- title:
--   P2 M Ground Theory Heights  Heights Four B gram eq 801d9bae3823: P2 M Ground Theory Heights  Heights Four B gram eq 801d9bae3823
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B gram eq 801d9bae3823 construction uses the P2 M Ground Theory Heights  Heights Four B gram eq 801d9bae3823 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L75-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L75-L96

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
variable {N : ℕ}
variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)

theorem P2M_GroundTheory_Heights__Heights_FourB_gram_eq_801d9bae3823 : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
    topPoly' i hi L * (sigTop p i hi).map C * topPoly i hi L +
      (X ^ 2 : ℂ[X]) • (tailForm p i hi L).map C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«gram_eq» := P2M_GroundTheory_Heights__Heights_FourB_gram_eq_801d9bae3823
