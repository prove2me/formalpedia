-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_chartMon_zero_9c1601a62faa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_chartMon_zero_9c1601a62faa
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:59.6079+00:00
-- url     : https://prove2.me/theorems/17a2793a-04cc-43c3-b8ce-b5df9278d845
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set chart Mon zero 9c1601a62faa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set chart Mon zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set chart Mon zero 9c1601a62faa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Heights Set chart Mon zero 9c1601a62faa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSmoothHermConstLine.lean#L120-L121

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_chartMon_zero_9c1601a62faa (c : (k : K) → ι k) : chartMon c 0 = (1 : MRing ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HeightsSet».«chartMon_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_chartMon_zero_9c1601a62faa
