-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_length_quot_map_of_surjective_9b9a1118e43f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_length_quot_map_of_surjective_9b9a1118e43f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:58.630804+00:00
-- url     : https://prove2.me/theorems/84daa688-981e-4db6-a624-ff857068bd47
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof length quot map of surjective 9b9a1118e43f: P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof length quot map of surjective 9b9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof length quot map of surjective 9b9a1118e43f construction uses the P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof length quot map of surjective 9b9a1118e43f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L14-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof

theorem P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_length_quot_map_of_surjective_9b9a1118e43f {L L' : Type*} [CommRing L] [CommRing L'] (θ : L →+* L')
    (hθ : Function.Surjective θ) (I : Ideal L) (hker : RingHom.ker θ ≤ I) :
    Module.length L' (L' ⧸ I.map θ) = Module.length L (L ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFFibreMultProof».«length_quot_map_of_surjective» := P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_length_quot_map_of_surjective_9b9a1118e43f
