-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjTopology_isOpen_iff_3d007405dc62
-- name    : P2M_GroundTheory_Heights__Heights_ProjTopology_isOpen_iff_3d007405dc62
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:18.445176+00:00
-- url     : https://prove2.me/theorems/43888b9c-d158-5bcc-893a-492574ce8c70
-- title:
--   P2 M Ground Theory Heights  Heights Proj Topology is Open iff 3d007405dc62: P2 M Ground Theory Heights  Heights Proj Topology is Open iff 3d007405dc62
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Topology is Open iff 3d007405dc62 construction uses the P2 M Ground Theory Heights  Heights Proj Topology is Open iff 3d007405dc62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ProjTopology.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ProjTopology.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ProjTopology
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
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
open GroundTheory.Heights₂.Heights.ProjTopology

theorem P2M_GroundTheory_Heights__Heights_ProjTopology_isOpen_iff_3d007405dc62 {s : Set (ℙ K V)} :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjTopology».«isOpen_iff» := P2M_GroundTheory_Heights__Heights_ProjTopology_isOpen_iff_3d007405dc62
