-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_comap_eq_maximalIdeal_cc86a5f9bf6a
-- name    : P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_comap_eq_maximalIdeal_cc86a5f9bf6a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:41.162536+00:00
-- url     : https://prove2.me/theorems/23412528-c014-4f36-916a-df388cbfb617
-- title:
--   P2 M Ground Theory Heights  Heights Length Finite Algebra comap eq maximal Ideal cc86a5f9bf6a: P2 M Ground Theory Heights  Heights Length Finite Algebra comap eq maximal Ideal cc86a5f9bf6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Finite Algebra comap eq maximal Ideal cc86a5f9bf6a construction uses the P2 M Ground Theory Heights  Heights Length Finite Algebra comap eq maximal Ideal cc86a5f9bf6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthFiniteAlgebra.lean#L15-L17

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

theorem P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_comap_eq_maximalIdeal_cc86a5f9bf6a [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    P.comap (algebraMap O B) = maximalIdeal O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthFiniteAlgebra».«comap_eq_maximalIdeal» := P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_comap_eq_maximalIdeal_cc86a5f9bf6a
