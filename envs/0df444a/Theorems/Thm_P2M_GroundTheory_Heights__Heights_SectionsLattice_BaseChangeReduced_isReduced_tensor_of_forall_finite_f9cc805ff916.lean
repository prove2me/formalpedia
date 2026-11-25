-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_finite_f9cc805ff916
-- name    : P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_finite_f9cc805ff916
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:18.921105+00:00
-- url     : https://prove2.me/theorems/00b17c32-6210-546e-a366-7ab3c574d930
-- title:
--   P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor of forall finite f9cc805ff916: P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Re
-- statement:
--   The P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor of forall finite f9cc805ff916 construction uses the P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor of forall finite f9cc805ff916 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/PBaseChangeReduced.lean#L41-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/PBaseChangeReduced.lean#L41-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_PBaseChangeReduced
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
open TensorProduct
open GroundTheory.Heights₂.Heights.SectionsLattice
open GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced

theorem P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_finite_f9cc805ff916 {k B : Type} [Field k] [CommRing B] [Algebra k B]
    (hB : ∀ (E : Type) [Field E] [Algebra k E] [FiniteDimensional k E], IsReduced (E ⊗[k] B))
    (A : Type) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (B ⊗[k] A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionsLattice».«BaseChangeReduced».«isReduced_tensor_of_forall_finite» := P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_finite_f9cc805ff916
