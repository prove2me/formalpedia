-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjTopology_continuous_iff_987b241a3e2f
-- name    : P2M_GroundTheory_Heights__Heights_ProjTopology_continuous_iff_987b241a3e2f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:23.030408+00:00
-- url     : https://prove2.me/theorems/f56f31b3-99cb-4945-8272-2461a4b1029e
-- title:
--   P2 M Ground Theory Heights  Heights Proj Topology continuous iff 987b241a3e2f: P2 M Ground Theory Heights  Heights Proj Topology continuous iff 987b241a3e2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Topology continuous iff 987b241a3e2f construction uses the P2 M Ground Theory Heights  Heights Proj Topology continuous iff 987b241a3e2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ProjTopology.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ProjTopology.lean#L26-L28

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

theorem P2M_GroundTheory_Heights__Heights_ProjTopology_continuous_iff_987b241a3e2f {Y : Type*} [TopologicalSpace Y] {g : ℙ K V → Y} :
    Continuous g ↔ Continuous (g ∘ Projectivization.mk' K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjTopology».«continuous_iff» := P2M_GroundTheory_Heights__Heights_ProjTopology_continuous_iff_987b241a3e2f
