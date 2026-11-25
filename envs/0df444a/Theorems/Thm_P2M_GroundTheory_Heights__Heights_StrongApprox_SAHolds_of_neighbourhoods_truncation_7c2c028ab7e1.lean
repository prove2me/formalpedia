-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_of_neighbourhoods_truncation_7c2c028ab7e1
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_of_neighbourhoods_truncation_7c2c028ab7e1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:33.653423+00:00
-- url     : https://prove2.me/theorems/92241cae-e252-45b0-a8ce-b1dbdd66f84b
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx SAHolds of neighbourhoods truncation 7c2c028ab7e1: P2 M Ground Theory Heights  Heights Strong Approx SAHolds of neighbourhoods truncation 7c2c028ab7e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx SAHolds of neighbourhoods truncation 7c2c028ab7e1 construction uses the P2 M Ground Theory Heights  Heights Strong Approx SAHolds of neighbourhoods truncation 7c2c028ab7e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAHolds.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAHolds.lean#L13-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAHolds
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
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_of_neighbourhoods_truncation_7c2c028ab7e1 (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«SAHolds».«of_neighbourhoods_truncation» := P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_of_neighbourhoods_truncation_7c2c028ab7e1
