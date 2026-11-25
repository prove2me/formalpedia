-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_apply_eq_88396f4fe788
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_apply_eq_88396f4fe788
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:33.532837+00:00
-- url     : https://prove2.me/theorems/71a5d09c-c68d-4b1a-acbe-fa59291d3aa3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations apply eq 88396f4fe788: P2 M Ground Theory Heights  Heights Inter Plucker Relations apply eq 88396f4fe788
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations apply eq 88396f4fe788 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations apply eq 88396f4fe788 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L47-L51

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_apply_eq_88396f4fe788 (ψ : S.E →ₗ[S.Ω] S.Ω) (u : S.E) :
    ψ u = S.e.repr u 0 * ψ (S.e 0) + S.e.repr u 1 * ψ (S.e 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«apply_eq» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_apply_eq_88396f4fe788
