-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_isMaximal_d262c3f82dfa
-- name    : P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_isMaximal_d262c3f82dfa
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:19.057829+00:00
-- url     : https://prove2.me/theorems/5768509a-67a2-4f5e-ac9b-cabfb709e3d1
-- title:
--   P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor of forall is Maximal d262c3f82dfa: P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced i
-- statement:
--   The P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor of forall is Maximal d262c3f82dfa construction uses the P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor of forall is Maximal d262c3f82dfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/PBaseChangeReduced.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/PBaseChangeReduced.lean#L13-L39

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

theorem P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_isMaximal_d262c3f82dfa {k R B : Type} [Field k] [CommRing R] [Algebra k R]
    [IsJacobsonRing R] [IsReduced R] [CommRing B] [Algebra k B]
    (h : ∀ m : Ideal R, m.IsMaximal → IsReduced ((R ⧸ m) ⊗[k] B)) : IsReduced (R ⊗[k] B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionsLattice».«BaseChangeReduced».«isReduced_tensor_of_forall_isMaximal» := P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_isMaximal_d262c3f82dfa
