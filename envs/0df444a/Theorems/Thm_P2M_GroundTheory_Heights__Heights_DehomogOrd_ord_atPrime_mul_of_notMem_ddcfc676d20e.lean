-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_mul_of_notMem_ddcfc676d20e
-- name    : P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_mul_of_notMem_ddcfc676d20e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:21.515347+00:00
-- url     : https://prove2.me/theorems/1a6d857d-5f73-5316-8f54-dbbb001ea059
-- title:
--   P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime mul of not Mem ddcfc676d20e: P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime mul of not Mem ddcfc676d20e
-- statement:
--   The P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime mul of not Mem ddcfc676d20e construction uses the P2 M Ground Theory Heights  Heights Dehomog Ord ord at Prime mul of not Mem ddcfc676d20e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L49-L56

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

theorem P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_mul_of_notMem_ddcfc676d20e {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] {u : A} (hu : u ∉ P)
    (x : A) :
    Ring.ord (Localization.AtPrime P) (algebraMap A _ (u * x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap A _ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DehomogOrd».«ord_atPrime_mul_of_notMem» := P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_mul_of_notMem_ddcfc676d20e
