-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059
-- name    : P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:52.450797+00:00
-- url     : https://prove2.me/theorems/405963aa-554c-4835-b734-67a5d35606e4
-- title:
--   P2 M Ground Theory Heights  Heights ord at Prime map localization 62a68cf88059: P2 M Ground Theory Heights  Heights ord at Prime map localization 62a68cf88059
-- statement:
--   The P2 M Ground Theory Heights  Heights ord at Prime map localization 62a68cf88059 construction uses the P2 M Ground Theory Heights  Heights ord at Prime map localization 62a68cf88059 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L37-L48

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

theorem P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059 {R : Type*} [CommRing R] (M : Submonoid R) (P : Ideal R)
    [hP : P.IsPrime] (hd : Disjoint (M : Set R) P) [hP' : (P.map (algebraMap R (Localization M))).IsPrime]
    (x : R) :
    Ring.ord (Localization.AtPrime (P.map (algebraMap R (Localization M))))
        (algebraMap (Localization M) _ (algebraMap R _ x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ord_atPrime_map_localization» := P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059
