-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_length_quot_map_of_flat_44aaab1f2176
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_length_quot_map_of_flat_44aaab1f2176
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:53.655118+00:00
-- url     : https://prove2.me/theorems/96814c9f-51f8-4b76-9c4d-15eb7c582a90
-- title:
--   P2 M Ground Theory Heights  Heights Vertical length quot map of flat 44aaab1f2176: P2 M Ground Theory Heights  Heights Vertical length quot map of flat 44aaab1f2176
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical length quot map of flat 44aaab1f2176 construction uses the P2 M Ground Theory Heights  Heights Vertical length quot map of flat 44aaab1f2176 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecLength.lean#L13-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecLength.lean#L13-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecLength
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_length_quot_map_of_flat_44aaab1f2176 {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (P J : Ideal A) (ψ : A ⧸ P →+* L)
    (hloc : IsLocalHom (ψ.comp (Ideal.Quotient.mk P))) (hflat : ψ.Flat)
    (hmax : (IsLocalRing.maximalIdeal A).map (ψ.comp (Ideal.Quotient.mk P)) =
      IsLocalRing.maximalIdeal L) :
    Module.length L (L ⧸ J.map (ψ.comp (Ideal.Quotient.mk P))) =
      Module.length A (A ⧸ (P ⊔ J)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«length_quot_map_of_flat» := P2M_GroundTheory_Heights__Heights_Vertical_length_quot_map_of_flat_44aaab1f2176
