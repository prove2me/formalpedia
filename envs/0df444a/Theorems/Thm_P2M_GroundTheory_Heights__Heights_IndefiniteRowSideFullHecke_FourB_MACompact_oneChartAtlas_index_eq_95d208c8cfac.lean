-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_index_eq_95d208c8cfac
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_index_eq_95d208c8cfac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:40.961968+00:00
-- url     : https://prove2.me/theorems/0bca98d1-4687-49cc-a650-570e1bd44cae
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact one Chart Atlas index eq 95d208c8cfac: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MAC
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact one Chart Atlas index eq 95d208c8cfac construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact one Chart Atlas index eq 95d208c8cfac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L66-L67

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_index_eq_95d208c8cfac (hΩ : IsOpen Ω) [Nonempty Ω] (j : Fin (oneChartAtlas hΩ).n) : j = j0 hΩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«MACompact».«oneChartAtlas_index_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_index_eq_95d208c8cfac
