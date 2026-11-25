-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_inter_tensor_535c04646f1c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_inter_tensor_535c04646f1c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:19:45.156656+00:00
-- url     : https://prove2.me/theorems/f2ba31d3-db00-5345-b9b1-1559bb876e93
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set inter tensor 535c04646f1c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set inter tensor 53
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set inter tensor 535c04646f1c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set inter tensor 535c04646f1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean#L242-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean#L242-L246

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_inter_tensor_535c04646f1c (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    {A B : Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    I W 1 ![A.tensor B] = I W 1 ![A] + I W 1 ![B] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«inter_tensor» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_inter_tensor_535c04646f1c
