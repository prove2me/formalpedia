-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_matGauss_matSub_099f3ef8c5f3
-- name    : P2M_GroundTheory_Heights__Heights_matGauss_matSub_099f3ef8c5f3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:18.463813+00:00
-- url     : https://prove2.me/theorems/5b4e7f00-0f6f-4f44-ab8d-8d98bab45abd
-- title:
--   P2 M Ground Theory Heights  Heights mat Gauss mat Sub 099f3ef8c5f3: P2 M Ground Theory Heights  Heights mat Gauss mat Sub 099f3ef8c5f3
-- statement:
--   The P2 M Ground Theory Heights  Heights mat Gauss mat Sub 099f3ef8c5f3 construction uses the P2 M Ground Theory Heights  Heights mat Gauss mat Sub 099f3ef8c5f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L102-L104

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

theorem P2M_GroundTheory_Heights__Heights_matGauss_matSub_099f3ef8c5f3 {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : matGauss (matSub U π) = matGauss π := by sorry

alias «GroundTheory».«Heights₂».«Heights».«matGauss_matSub» := P2M_GroundTheory_Heights__Heights_matGauss_matSub_099f3ef8c5f3
