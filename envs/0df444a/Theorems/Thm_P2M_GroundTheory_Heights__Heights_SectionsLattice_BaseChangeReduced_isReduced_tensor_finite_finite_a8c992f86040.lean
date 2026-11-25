-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_finite_finite_a8c992f86040
-- name    : P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_finite_finite_a8c992f86040
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:13.095041+00:00
-- url     : https://prove2.me/theorems/4ab1340c-802e-5c2e-b99d-dd870f846b8c
-- title:
--   P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor finite finite a8c992f86040: P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduc
-- statement:
--   The P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor finite finite a8c992f86040 construction uses the P2 M Ground Theory Heights  Heights Sections Lattice Base Change Reduced is Reduced tensor finite finite a8c992f86040 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/PBaseChangeReduced.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ReducedTensors/PBaseChangeReduced.lean#L56-L60

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

theorem P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_finite_finite_a8c992f86040 {k : Type} [Field k] [CharZero k] (E E' : Type) [Field E]
    [Algebra k E] [Field E'] [Algebra k E'] [FiniteDimensional k E'] :
    IsReduced (E ⊗[k] E') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionsLattice».«BaseChangeReduced».«isReduced_tensor_finite_finite» := P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_finite_finite_a8c992f86040
