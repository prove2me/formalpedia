-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687
-- name    : P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:41.95406+00:00
-- url     : https://prove2.me/theorems/ad421960-042d-4a85-86c2-b5bde8a492ff
-- title:
--   P2 M Ground Theory Heights  Heights Slice Bundle Radical Away coeff Map comp map C 04b3d0cca687: P2 M Ground Theory Heights  Heights Slice Bundle Radical Away coeff Map comp map C 04b3d0cca687
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Bundle Radical Away coeff Map comp map C 04b3d0cca687 construction uses the P2 M Ground Theory Heights  Heights Slice Bundle Radical Away coeff Map comp map C 04b3d0cca687 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L98-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)

theorem P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687 :
    (solveMap J d q k).comp (MvPolynomial.map C) = C.comp (toBase J q k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceBundleRadicalAway».«coeffMap_comp_mapC» := P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_coeffMap_comp_mapC_04b3d0cca687
