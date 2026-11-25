-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_comp_solveMap_b92ab9c7e078
-- name    : P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_comp_solveMap_b92ab9c7e078
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:36.697223+00:00
-- url     : https://prove2.me/theorems/7fedc730-be09-4a21-859c-2f1fa514d653
-- title:
--   P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map comp solve Map b92ab9c7e078: P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map comp solve Map b92ab9c7e078
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map comp solve Map b92ab9c7e078 construction uses the P2 M Ground Theory Heights  Heights Slice Bundle Radical Away back Map comp solve Map b92ab9c7e078 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L81-L96

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

theorem P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_comp_solveMap_b92ab9c7e078 : (backMap J d q k).comp (solveMap J d q k) = toTot J d q k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceBundleRadicalAway».«backMap_comp_solveMap» := P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_backMap_comp_solveMap_b92ab9c7e078
