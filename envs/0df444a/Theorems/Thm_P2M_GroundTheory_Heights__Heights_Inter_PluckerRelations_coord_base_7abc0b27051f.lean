-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_coord_base_7abc0b27051f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_coord_base_7abc0b27051f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:07.2044+00:00
-- url     : https://prove2.me/theorems/2cfa5aa5-5df7-460e-932f-cbb6b6ed22e5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Relations coord base 7abc0b27051f: P2 M Ground Theory Heights  Heights Inter Plucker Relations coord base 7abc0b27051f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Relations coord base 7abc0b27051f construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Relations coord base 7abc0b27051f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean#L88-L90

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_coord_base_7abc0b27051f (j : S.ι) :
    T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1) ⟨T.WBlk.base, j⟩ = algebraMap S.Ω S.Φ (S.x j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerRelations».«coord_base» := P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_coord_base_7abc0b27051f
