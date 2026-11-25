-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosurePullback_proof_3a1b11bde3ff
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosurePullback_proof_3a1b11bde3ff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:07.866787+00:00
-- url     : https://prove2.me/theorems/d28541ab-9ba4-4100-99d7-78bc189488c9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Pullback proof 3a1b11bde3ff: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Pullback proof 3a1b11bde3ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Pullback proof 3a1b11bde3ff construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Closure Pullback proof 3a1b11bde3ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L160-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L160-L241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosurePullback_proof_3a1b11bde3ff (hPull : PairNumberPullback.Statement)
    (hExp : PairNumberExpansionIndependence.Statement) (hMod : SegreFlagClosureModel.Statement)
    (hRel : PairNumberRelabel.Statement) (hVJ : VerticalDivisorJoinPullback.Statement)
    (hBir : SegreFlagClosureBirational.Statement) : SegreFlagClosurePullback.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagClosurePullback».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosurePullback_proof_3a1b11bde3ff
