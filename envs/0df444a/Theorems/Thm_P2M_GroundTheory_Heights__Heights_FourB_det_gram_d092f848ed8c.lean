-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_det_gram_d092f848ed8c
-- name    : P2M_GroundTheory_Heights__Heights_FourB_det_gram_d092f848ed8c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:52.341646+00:00
-- url     : https://prove2.me/theorems/fc9dfe91-1c35-5af3-8683-d4ca28e94939
-- title:
--   P2 M Ground Theory Heights  Heights Four B det gram d092f848ed8c: P2 M Ground Theory Heights  Heights Four B det gram d092f848ed8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B det gram d092f848ed8c construction uses the P2 M Ground Theory Heights  Heights Four B det gram d092f848ed8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L133-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L133-L156

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
variable {L}

theorem P2M_GroundTheory_Heights__Heights_FourB_det_gram_d092f848ed8c (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) :
    (rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L).det =
      C (sigTop p i hi).det * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«det_gram» := P2M_GroundTheory_Heights__Heights_FourB_det_gram_d092f848ed8c
