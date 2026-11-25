-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussDualMin_inner_toLp_eq_dotProduct_e8491acdea74
-- name    : P2M_GroundTheory_Heights__Heights_PGaussDualMin_inner_toLp_eq_dotProduct_e8491acdea74
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:57.635751+00:00
-- url     : https://prove2.me/theorems/5fa700d7-9b13-4659-9690-bf1f58ddfb58
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Dual Min inner to Lp eq dot Product e8491acdea74: P2 M Ground Theory Heights  Heights PGauss Dual Min inner to Lp eq dot Product e8491acdea74
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Dual Min inner to Lp eq dot Product e8491acdea74 construction uses the P2 M Ground Theory Heights  Heights PGauss Dual Min inner to Lp eq dot Product e8491acdea74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussDualMin.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussDualMin.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussDualMin
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
open Matrix
open GroundTheory.Heights₂.Heights.PGaussDualMin

theorem P2M_GroundTheory_Heights__Heights_PGaussDualMin_inner_toLp_eq_dotProduct_e8491acdea74 {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussDualMin».«inner_toLp_eq_dotProduct» := P2M_GroundTheory_Heights__Heights_PGaussDualMin_inner_toLp_eq_dotProduct_e8491acdea74
