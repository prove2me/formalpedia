-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_proof_27abaefb27c3
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_proof_27abaefb27c3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:57:22.112469+00:00
-- url     : https://prove2.me/theorems/33cd50f1-2898-4622-bd83-78a56989af9c
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative proof 27abaefb27c3: P2 M Ground Theory Heights  Heights Regular Hodge Derivative proof 27abaefb27c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative proof 27abaefb27c3 construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative proof 27abaefb27c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L197-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L197-L362

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartBounds_proof_40793fde9b4d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open HodgeDerivative

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_proof_27abaefb27c3 (h0 : ImTauBounds.Statement) (h1 : Tau0Holomorphic.Statement)
    (hAn : AnalyticDerivBound.Statement) (hInv : InvEntryDeriv.Statement)
    (hLDG : LogDetGramDeriv.Statement) : HodgeDerivative.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«proof» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_proof_27abaefb27c3
