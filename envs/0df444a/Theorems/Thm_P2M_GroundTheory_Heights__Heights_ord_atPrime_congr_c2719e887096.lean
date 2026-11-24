-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096
-- name    : P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:54.534803+00:00
-- url     : https://prove2.me/theorems/bfb2e7b7-bf36-40fb-bb19-c3f9fc6e2588
-- title:
--   P2 M Ground Theory Heights  Heights ord at Prime congr c2719e887096: P2 M Ground Theory Heights  Heights ord at Prime congr c2719e887096
-- statement:
--   The P2 M Ground Theory Heights  Heights ord at Prime congr c2719e887096 construction uses the P2 M Ground Theory Heights  Heights ord at Prime congr c2719e887096 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L31-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
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

theorem P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096 {R : Type*} [CommRing R] {P₁ P₂ : Ideal R} [P₁.IsPrime] [P₂.IsPrime]
    (h : P₁ = P₂) (x : R) :
    Ring.ord (Localization.AtPrime P₁) (algebraMap R _ x) =
      Ring.ord (Localization.AtPrime P₂) (algebraMap R _ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ord_atPrime_congr» := P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096
