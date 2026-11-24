-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:02.076845+00:00
-- url     : https://prove2.me/theorems/5f00d2d0-079d-4fe7-8c10-c3e449da6888
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover yyc base 29c3d2390e14: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover yyc base 29c3d2390e14
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover yyc base 29c3d2390e14 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover yyc base 29c3d2390e14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L230-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L230-L230

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14 (i : S.ι) : yyc S ⟨.base, i⟩ = algebraMap S.Ω S.Φ (S.x i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«yyc_base» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14
