-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zariskiDense_iff_orbitIdeal_c5276589b00e
-- name    : P2M_GroundTheory_Heights__Heights_zariskiDense_iff_orbitIdeal_c5276589b00e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:54.958958+00:00
-- url     : https://prove2.me/theorems/7f515554-acf4-4a96-856a-0e918ad3959e
-- title:
--   P2 M Ground Theory Heights  Heights zariski Dense iff orbit Ideal c5276589b00e: P2 M Ground Theory Heights  Heights zariski Dense iff orbit Ideal c5276589b00e
-- statement:
--   The P2 M Ground Theory Heights  Heights zariski Dense iff orbit Ideal c5276589b00e construction uses the P2 M Ground Theory Heights  Heights zariski Dense iff orbit Ideal c5276589b00e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L128-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L128-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_zariskiDense_iff_orbitIdeal_c5276589b00e (P : ArithVariety n) (S : Set (Cone n (AlgebraicClosure ℚ))) :
    P.ZariskiDense S ↔ Geo.IsZariskiDense (ι := blockIdx n) P.ideal (orbitIdeal '' S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zariskiDense_iff_orbitIdeal» := P2M_GroundTheory_Heights__Heights_zariskiDense_iff_orbitIdeal_c5276589b00e
