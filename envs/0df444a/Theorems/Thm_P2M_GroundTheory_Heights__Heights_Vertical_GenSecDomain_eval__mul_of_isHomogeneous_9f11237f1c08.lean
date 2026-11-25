-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__mul_of_isHomogeneous_9f11237f1c08
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__mul_of_isHomogeneous_9f11237f1c08
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:11.110836+00:00
-- url     : https://prove2.me/theorems/6468cd99-9c31-55db-b583-e66b81a2a171
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  mul of is Homogeneous 9f11237f1c08: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  mul of is Homogeneous 9f11237f1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  mul of is Homogeneous 9f11237f1c08 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain eval  mul of is Homogeneous 9f11237f1c08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L16-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__mul_of_isHomogeneous_9f11237f1c08 {k S : Type*} [CommSemiring k] [CommSemiring S] {n : ℕ} (f : k →+* S)
    (x : Fin n → S) (a : S) {q : MvPolynomial (Fin n) k} {d : ℕ} (hq : q.IsHomogeneous d) :
    eval₂ f (fun l => x l * a) q = a ^ d * eval₂ f x q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«eval₂_mul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__mul_of_isHomogeneous_9f11237f1c08
