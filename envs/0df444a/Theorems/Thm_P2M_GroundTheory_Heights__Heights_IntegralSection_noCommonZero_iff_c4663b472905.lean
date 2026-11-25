-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralSection_noCommonZero_iff_c4663b472905
-- name    : P2M_GroundTheory_Heights__Heights_IntegralSection_noCommonZero_iff_c4663b472905
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:26:15.186254+00:00
-- url     : https://prove2.me/theorems/cb72e2d0-2137-5c24-8397-a51b23f48712
-- title:
--   P2 M Ground Theory Heights  Heights Integral Section no Common Zero iff c4663b472905: P2 M Ground Theory Heights  Heights Integral Section no Common Zero iff c4663b472905
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Section no Common Zero iff c4663b472905 construction uses the P2 M Ground Theory Heights  Heights Integral Section no Common Zero iff c4663b472905 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L568-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L568-L574

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

theorem P2M_GroundTheory_Heights__Heights_IntegralSection_noCommonZero_iff_c4663b472905 (hS : NoCommonZeroComplex.Statement)
    {P : ArithVariety n} {a : ι → ℤ} {J : ℕ} (s : Fin J → IntegralSection P a)
    {Ω : Type*} [Field Ω] {y : Coord n → Ω} (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) :
    IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a (fun j ↦ (s j).valueAt y) ↔
      ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralSection».«noCommonZero_iff» := P2M_GroundTheory_Heights__Heights_IntegralSection_noCommonZero_iff_c4663b472905
