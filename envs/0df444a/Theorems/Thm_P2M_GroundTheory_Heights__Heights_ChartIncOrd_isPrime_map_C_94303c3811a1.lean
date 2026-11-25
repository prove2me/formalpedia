-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_isPrime_map_C_94303c3811a1
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncOrd_isPrime_map_C_94303c3811a1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:55.794363+00:00
-- url     : https://prove2.me/theorems/c9be75a8-585b-4ed8-871e-2b6d05ae38c0
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Ord is Prime map C 94303c3811a1: P2 M Ground Theory Heights  Heights Chart Inc Ord is Prime map C 94303c3811a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Ord is Prime map C 94303c3811a1 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Ord is Prime map C 94303c3811a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncOrd

theorem P2M_GroundTheory_Heights__Heights_ChartIncOrd_isPrime_map_C_94303c3811a1 {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (p.map (C : R →+* MvPolynomial σ R)).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncOrd».«isPrime_map_C» := P2M_GroundTheory_Heights__Heights_ChartIncOrd_isPrime_map_C_94303c3811a1
