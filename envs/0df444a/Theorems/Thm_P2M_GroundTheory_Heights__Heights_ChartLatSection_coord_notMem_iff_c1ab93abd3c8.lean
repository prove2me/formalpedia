-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_coord_notMem_iff_c1ab93abd3c8
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_coord_notMem_iff_c1ab93abd3c8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:31.747069+00:00
-- url     : https://prove2.me/theorems/89fc3160-6b23-4b22-9e44-954da84a6bdd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section coord not Mem iff c1ab93abd3c8: P2 M Ground Theory Heights  Heights Chart Lat Section coord not Mem iff c1ab93abd3c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section coord not Mem iff c1ab93abd3c8 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section coord not Mem iff c1ab93abd3c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L65-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_coord_notMem_iff_c1ab93abd3c8 (y : Coord n → Ω) {P : ArithVariety n}
    (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (p : Coord n) :
    (X p : MvPolynomial (Coord n) ℤ) ∉ P.ideal ↔ y p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«coord_notMem_iff» := P2M_GroundTheory_Heights__Heights_ChartLatSection_coord_notMem_iff_c1ab93abd3c8
