-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_of_80384e316f32
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_of_80384e316f32
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:42.205079+00:00
-- url     : https://prove2.me/theorems/d590b7a8-1749-4c77-a8ac-fdc57ddde332
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numbers agree of 80384e316f32: P2 M Ground Theory Heights  Heights Numbers DVR Numbers agree of 80384e316f32
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numbers agree of 80384e316f32 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numbers agree of 80384e316f32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsFieldIntersectionExample.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsFieldIntersectionExample.lean#L115-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumIsFieldIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_of_80384e316f32 (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u}) (I : IFamily F ι)
    (hI : IsFieldIntersection I) (V : Ideal (MRingOver F ι)) (n : ℕ) (L : Fin n → K → ℤ)
    (hV : IsProjVarF V n) : I V n L = intNum F V L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Numbers».«agree_of» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_of_80384e316f32
