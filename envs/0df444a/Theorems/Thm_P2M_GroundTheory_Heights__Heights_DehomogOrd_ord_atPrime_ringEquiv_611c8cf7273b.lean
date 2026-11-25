-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_ringEquiv_611c8cf7273b
-- name    : P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_ringEquiv_611c8cf7273b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:40.89137+00:00
-- url     : https://prove2.me/theorems/7c09b857-00b2-5935-a5af-b52f9fa2fcae
-- title:
--   P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime ring Equiv 611c8cf7273b: P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime ring Equiv 611c8cf7273b
-- statement:
--   The P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime ring Equiv 611c8cf7273b construction uses the P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime ring Equiv 611c8cf7273b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L15-L35

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

theorem P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_ringEquiv_611c8cf7273b {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) (P : Ideal S)
    (P' : Ideal T) [P.IsPrime] [P'.IsPrime] (h : ∀ y, y ∈ P' ↔ e.symm y ∈ P) (x : S) :
    Ring.ord (Localization.AtPrime P') (algebraMap T _ (e x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap S _ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DehomogOrd».«ord_atPrime_ringEquiv» := P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_ringEquiv_611c8cf7273b
