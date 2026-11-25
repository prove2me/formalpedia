-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_linForm_b42ca2da91cd
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_linForm_b42ca2da91cd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:58.109098+00:00
-- url     : https://prove2.me/theorems/8379f089-f1da-51f5-8b7b-15241a438fc4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map lin Form b42ca2da91cd: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map lin Form b42ca2da91cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map lin Form b42ca2da91cd construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain map lin Form b42ca2da91cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_linForm_b42ca2da91cd {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«map_linForm» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_map_linForm_b42ca2da91cd
