-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653
-- name    : P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:28.795804+00:00
-- url     : https://prove2.me/theorems/f53c11f2-1cb5-456e-a6b7-052498ce0526
-- title:
--   P2 M Ground Theory Heights  Heights Slice Bundle Radical Away base To Tot to Base ac1c06484653: P2 M Ground Theory Heights  Heights Slice Bundle Radical Away base To Tot to Base ac1c06484653
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Bundle Radical Away base To Tot to Base ac1c06484653 construction uses the P2 M Ground Theory Heights  Heights Slice Bundle Radical Away base To Tot to Base ac1c06484653 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L68-L70

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

theorem P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653 (a : MvPolynomial (Fin n) ℂ) :
    baseToTot J d q k (toBase J q k a) = toTot J d q k (MvPolynomial.map C a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceBundleRadicalAway».«baseToTot_toBase» := P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_baseToTot_toBase_ac1c06484653
