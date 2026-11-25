-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_continuousOn_f7eedd4e6ecd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_continuousOn_f7eedd4e6ecd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:33.253024+00:00
-- url     : https://prove2.me/theorems/7c408e1b-08a2-4276-b218-7d046763188a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact top Dens continuous On f7eedd4e6ecd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACom
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact top Dens continuous On f7eedd4e6ecd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact top Dens continuous On f7eedd4e6ecd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L32-L37

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_continuousOn_f7eedd4e6ecd {ψ : (Fin D → ℂ) → ℝ} (hΩ : IsOpen Ω) (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    ContinuousOn (topDens ψ) Ω := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«MACompact».«topDens_continuousOn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_continuousOn_f7eedd4e6ecd
