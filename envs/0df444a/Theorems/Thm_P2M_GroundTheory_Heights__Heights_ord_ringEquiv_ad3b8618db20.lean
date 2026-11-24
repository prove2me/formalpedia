-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20
-- name    : P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:50.836264+00:00
-- url     : https://prove2.me/theorems/5e4b96fd-b1e9-4523-8834-72196fc58d82
-- title:
--   P2 M Ground Theory Heights  Heights ord ring Equiv ad3b8618db20: P2 M Ground Theory Heights  Heights ord ring Equiv ad3b8618db20
-- statement:
--   The P2 M Ground Theory Heights  Heights ord ring Equiv ad3b8618db20 construction uses the P2 M Ground Theory Heights  Heights ord ring Equiv ad3b8618db20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocalOrder.lean#L13-L29

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

theorem P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20 {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ord_ringEquiv» := P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20
