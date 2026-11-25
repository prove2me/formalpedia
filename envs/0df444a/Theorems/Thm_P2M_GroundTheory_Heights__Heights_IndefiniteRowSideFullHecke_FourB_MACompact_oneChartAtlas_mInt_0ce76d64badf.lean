-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_mInt_0ce76d64badf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_mInt_0ce76d64badf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:09.705127+00:00
-- url     : https://prove2.me/theorems/7ff6667d-d3d5-516e-9ed3-33d7a7fe1311
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact one Chart Atlas m Int 0ce76d64badf: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MAComp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact one Chart Atlas m Int 0ce76d64badf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact one Chart Atlas m Int 0ce76d64badf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L79-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L79-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_mInt_0ce76d64badf (hΩ : IsOpen Ω) [Nonempty Ω] (Φ : Fin D → LocPot Ω) (g : Ω → ℝ) :
    mInt (oneChartAtlas hΩ) Φ g =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«MACompact».«oneChartAtlas_mInt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_mInt_0ce76d64badf
