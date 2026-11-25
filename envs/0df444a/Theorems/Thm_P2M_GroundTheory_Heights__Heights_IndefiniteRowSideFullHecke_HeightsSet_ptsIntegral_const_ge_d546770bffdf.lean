-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_ptsIntegral_const_ge_d546770bffdf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_ptsIntegral_const_ge_d546770bffdf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:10.255453+00:00
-- url     : https://prove2.me/theorems/f53b161f-53df-49f6-8b73-4685e7ba2d51
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set pts Integral const ge d546770bffdf: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set pts In
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set pts Integral const ge d546770bffdf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set pts Integral const ge d546770bffdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean#L159-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean#L159-L208

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_ptsIntegral_const_ge_d546770bffdf (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {t : ℝ}
    (ht : t ≤ 0) (hP : 0 < degC P) : t * degC P ≤ ptsIntegral P φ (fun _ ↦ t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«ptsIntegral_const_ge» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_ptsIntegral_const_ge_d546770bffdf
