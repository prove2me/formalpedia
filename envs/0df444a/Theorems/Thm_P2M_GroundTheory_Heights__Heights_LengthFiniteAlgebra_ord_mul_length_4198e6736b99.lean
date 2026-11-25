-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_ord_mul_length_4198e6736b99
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_ord_mul_length_4198e6736b99
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:01.898516+00:00
-- url     : https://prove2.me/theorems/d0d9e941-bf8e-4912-b4eb-e4574c214624
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra ord mul length 4198e6736b99: P2 M Ground Theory Heights  Heights Length Finite Algebra ord mul length 4198e6736b99
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra ord mul length 4198e6736b99 construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra ord mul length 4198e6736b99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L74-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L74-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
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
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_ord_mul_length_4198e6736b99 [Module.Finite O B] (P : Ideal B) [P.IsMaximal] (θ : B) :
    Ring.ord (Localization.AtPrime P) (algebraMap B _ θ) * Module.length O (B ⧸ P) =
      Module.length O (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) θ}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«ord_mul_length» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_ord_mul_length_4198e6736b99
