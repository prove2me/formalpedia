-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:26.107416+00:00
-- url     : https://prove2.me/theorems/74ec261d-5ccd-429c-a9cb-a21dad2b4430
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections from Spec mem de0322f741f7: P2 M Ground Theory Heights  Heights Model Height One Sections from Spec mem de0322f741f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections from Spec mem de0322f741f7 construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections from Spec mem de0322f741f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
omit [IsIntegral X]

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7 {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec p ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«fromSpec_mem» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7
