-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0
-- name    : P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:36.795427+00:00
-- url     : https://prove2.me/theorems/b6d418d0-af48-4c49-9429-f923ecf45241
-- title:
--   P2 M Ground Theory Heights  Heights KLines Quot Index ker coord Proj eba1c16731d0: P2 M Ground Theory Heights  Heights KLines Quot Index ker coord Proj eba1c16731d0
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Quot Index ker coord Proj eba1c16731d0 construction uses the P2 M Ground Theory Heights  Heights KLines Quot Index ker coord Proj eba1c16731d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndex.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesQuotIndex.lean#L23-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
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
open NumberField
open GroundTheory.Heights₂.Heights.KLinesQuotIndex

theorem P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0 {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) :
    LinearMap.ker (coordProj B) = Submodule.span K (Set.range fun i => B (Sum.inl i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesQuotIndex».«ker_coordProj» := P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0
