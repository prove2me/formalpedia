-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_disjoint_powers_ad65955fa1d4
-- name    : P2M_GroundTheory_Heights__Heights_DehomogOrd_disjoint_powers_ad65955fa1d4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:36.852936+00:00
-- url     : https://prove2.me/theorems/2379f2a6-b75a-5125-8c86-4cab55c5f14f
-- title:
--   P2 M Ground Theory Heights  Heights Dehomog Ord disjoint powers ad65955fa1d4: P2 M Ground Theory Heights  Heights Dehomog Ord disjoint powers ad65955fa1d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Dehomog Ord disjoint powers ad65955fa1d4 construction uses the P2 M Ground Theory Heights  Heights Dehomog Ord disjoint powers ad65955fa1d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L43-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
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
open GroundTheory.Heights₂.Heights.DehomogOrd

theorem P2M_GroundTheory_Heights__Heights_DehomogOrd_disjoint_powers_ad65955fa1d4 {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {x : R} (hx : x ∉ P) :
    Disjoint ((Submonoid.powers x : Submonoid R) : Set R) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DehomogOrd».«disjoint_powers» := P2M_GroundTheory_Heights__Heights_DehomogOrd_disjoint_powers_ad65955fa1d4
