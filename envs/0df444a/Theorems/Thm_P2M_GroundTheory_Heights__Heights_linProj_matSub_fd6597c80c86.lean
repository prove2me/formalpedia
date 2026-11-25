-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_matSub_fd6597c80c86
-- name    : P2M_GroundTheory_Heights__Heights_linProj_matSub_fd6597c80c86
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:36.356103+00:00
-- url     : https://prove2.me/theorems/64724662-ad3f-561c-b322-34fd0ea09e1c
-- title:
--   P2 M Ground Theory Heights  Heights lin Proj mat Sub fd6597c80c86: P2 M Ground Theory Heights  Heights lin Proj mat Sub fd6597c80c86
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Proj mat Sub fd6597c80c86 construction uses the P2 M Ground Theory Heights  Heights lin Proj mat Sub fd6597c80c86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L93-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L93-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_linProj_matSub_fd6597c80c86 {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    linProj (matSub U π) v = linProj π (U v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linProj_matSub» := P2M_GroundTheory_Heights__Heights_linProj_matSub_fd6597c80c86
