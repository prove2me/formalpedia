-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:59.240557+00:00
-- url     : https://prove2.me/theorems/01580f49-2f82-4ecc-bcda-25229a7ae1a5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend aeval mk map 8e48c39d9389: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend aeval mk map 8e48c39d9389
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend aeval mk map 8e48c39d9389 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend aeval mk map 8e48c39d9389 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389 (θ : B) (I : Ideal A) (P : A[X]) :
    aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (aeval θ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«aeval_mk_map» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389
