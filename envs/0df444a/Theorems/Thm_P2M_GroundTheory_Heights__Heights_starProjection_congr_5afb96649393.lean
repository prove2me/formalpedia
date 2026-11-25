-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_starProjection_congr_5afb96649393
-- name    : P2M_GroundTheory_Heights__Heights_starProjection_congr_5afb96649393
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:42.496473+00:00
-- url     : https://prove2.me/theorems/f08101ed-d360-4856-8a08-db9571a050cc
-- title:
--   P2 M Ground Theory Heights  Heights star Projection congr 5afb96649393: P2 M Ground Theory Heights  Heights star Projection congr 5afb96649393
-- statement:
--   The P2 M Ground Theory Heights  Heights star Projection congr 5afb96649393 construction uses the P2 M Ground Theory Heights  Heights star Projection congr 5afb96649393 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L91-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
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
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_starProjection_congr_5afb96649393 {U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} (e : U = V) :
    U.starProjection = V.starProjection := by sorry

alias «GroundTheory».«Heights₂».«Heights».«starProjection_congr» := P2M_GroundTheory_Heights__Heights_starProjection_congr_5afb96649393
