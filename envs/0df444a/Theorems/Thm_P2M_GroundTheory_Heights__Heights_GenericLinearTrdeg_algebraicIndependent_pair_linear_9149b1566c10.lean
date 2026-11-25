-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_pair_linear_9149b1566c10
-- name    : P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_pair_linear_9149b1566c10
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:55.287084+00:00
-- url     : https://prove2.me/theorems/8dd7e60d-8800-4214-9ff1-27bd80e144f5
-- title:
--   P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent pair linear 9149b1566c10: P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent pair linear 9149
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent pair linear 9149b1566c10 construction uses the P2 M Ground Theory Heights  Heights Generic Linear Trdeg algebraic Independent pair linear 9149b1566c10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L28-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L28-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
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
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg

theorem P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_pair_linear_9149b1566c10 {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] {η r x : A} (hη : Transcendental R η)
    (hx : Transcendental (Algebra.adjoin R ({η, r} : Set A)) x) :
    AlgebraicIndependent R ![x, x * η + r] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericLinearTrdeg».«algebraicIndependent_pair_linear» := P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_pair_linear_9149b1566c10
