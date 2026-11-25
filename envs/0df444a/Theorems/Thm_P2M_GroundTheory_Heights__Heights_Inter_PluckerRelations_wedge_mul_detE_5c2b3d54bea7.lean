-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_detE_5c2b3d54bea7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_detE_5c2b3d54bea7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:50.394282+00:00
-- url     : https://prove2.me/theorems/41e1b905-0d71-5107-981f-c4cb85ef5f6d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul det E 5c2b3d54bea7: P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul det E 5c2b3d54bea7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul det E 5c2b3d54bea7 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations wedge mul det E 5c2b3d54bea7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L53-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_detE_5c2b3d54bea7 (k m : S.κ) (u w : S.E) :
    wedgeVal S k m * T.detE S.e u w = S.φ k u * S.φ m w - S.φ k w * S.φ m u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«wedge_mul_detE» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_detE_5c2b3d54bea7
